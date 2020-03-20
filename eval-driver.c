#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>
#include "z3-fuzzy.h"
#include "utility/pretty-print.h"
static_assert(Z3_VERSION == 487, "This executable requires z3 4.8.7+");

#define NUM_ITERATIONS 1000

fuzzy_ctx_t fctx;

static inline unsigned long compute_time_usec(struct timeval* start,
                                              struct timeval* end)
{
    return ((end->tv_sec - start->tv_sec) * 1000000 + end->tv_usec -
            start->tv_usec);
}

static inline void usage(char* filename)
{
    fprintf(stderr, "wrong argv. usage:\n%s query_filename seed\n", filename);
    exit(1);
}

int main(int argc, char* argv[])
{
    if (argc < 2)
        usage(argv[0]);

    char*          query_filename = argv[1];
    char*          seed_filename  = argv[2];
    Z3_config      cfg            = Z3_mk_config();
    Z3_context     ctx            = Z3_mk_context(cfg);
    Z3_ast         query;
    Z3_ast*        str_symbols;
    char           var_name[128];
    Z3_sort        bsort = Z3_mk_bv_sort(ctx, 8);
    struct timeval stop, start;
    unsigned long  elapsed_time_z3 = 0, elapsed_time_fast = 0;
    unsigned long  num_queries;
    unsigned long  res1, res2;
    unsigned int   i;
    int            n;

    pp_init();
    z3fuzz_init(&fctx, ctx, seed_filename, NULL, NULL);

    str_symbols = (Z3_ast*)malloc(sizeof(Z3_ast) * fctx.n_symbols);
    for (i = 0; i < fctx.n_symbols; ++i) {
        n = snprintf(var_name, sizeof(var_name), "k!%u", i);
        assert(n > 0 && n < sizeof(var_name) && "symbol name too long");
        Z3_symbol s    = Z3_mk_string_symbol(ctx, var_name);
        Z3_ast    s_bv = Z3_mk_const(ctx, s, bsort);
        str_symbols[i] = s_bv;
    }

    Z3_ast_vector queries =
        Z3_parse_smtlib2_file(ctx, query_filename, 0, 0, 0, 0, 0, 0);
    Z3_ast_vector_inc_ref(ctx, queries);

    num_queries = Z3_ast_vector_size(ctx, queries);
    assert(num_queries == 1 && "only one query is allowed");

    testcase_t* testcase = &fctx.testcases.data[0];
    query                = Z3_ast_vector_get(ctx, queries, 0);
    query =
        Z3_substitute(ctx, query, fctx.n_symbols, str_symbols, fctx.symbols);
    Z3_ast_vector_dec_ref(ctx, queries);

    for (i = 0; i < NUM_ITERATIONS; ++i) {
        pp_printf(0, 1, "iteration %d/%d", i, NUM_ITERATIONS);

        gettimeofday(&start, NULL);
        res1 = z3fuzz_evaluate_expression(&fctx, query, testcase->bytes);
        gettimeofday(&stop, NULL);
        elapsed_time_fast += compute_time_usec(&start, &stop);

        gettimeofday(&start, NULL);
        res2 = z3fuzz_evaluate_expression_z3(&fctx, query, testcase->z3_bytes);
        gettimeofday(&stop, NULL);
        elapsed_time_z3 += compute_time_usec(&start, &stop);

        assert(res1 == res2 && "bug in evaluate!");
    }

    z3fuzz_free(&fctx);

    pp_set_col(0);
    pp_set_line(3);

    printf("Res: 0x%lx\n", res1);
    printf("Elapsed time fast:\t%ld usec\n", elapsed_time_fast / 1000);
    printf("Elapsed time z3:\t%ld usec\n", elapsed_time_z3 / 1000);

    return 0;
}
