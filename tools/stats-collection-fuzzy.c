#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>
#include "pretty-print.h"
#include "z3-fuzzy.h"

#define LOG_ON_FILE
#define FUZZY_SOLVER_TIMEOUT 1000

fuzzy_ctx_t fctx;
const char* log_filename = "fuzzy_queries.csv";
FILE*       log_file;
const char* flip_info_filename = "fuzzy_flip_info.csv";
FILE*       flip_info_file;

static inline double compute_time_msec(struct timeval* start,
                                       struct timeval* end)
{
    return ((end->tv_sec - start->tv_sec) * 1000000 + end->tv_usec -
            start->tv_usec) /
           1000.0L;
}

static inline Z3_ast find_branch_condition(Z3_ast query)
{
    if (Z3_get_ast_kind(fctx.z3_ctx, query) != Z3_APP_AST)
        return query;

    Z3_app       app       = Z3_to_app(fctx.z3_ctx, query);
    Z3_func_decl decl      = Z3_get_app_decl(fctx.z3_ctx, app);
    Z3_decl_kind decl_kind = Z3_get_decl_kind(fctx.z3_ctx, decl);
    if (decl_kind != Z3_OP_AND)
        return query;

    return Z3_get_app_arg(fctx.z3_ctx, app, 0);
}

static inline void divide_query_in_assertions(Z3_ast query, Z3_ast** assertions,
                                              unsigned* n)
{
    if (Z3_get_ast_kind(fctx.z3_ctx, query) != Z3_APP_AST) {
        *assertions = NULL;
        *n          = 0;
        return;
    }

    Z3_app       app       = Z3_to_app(fctx.z3_ctx, query);
    Z3_func_decl decl      = Z3_get_app_decl(fctx.z3_ctx, app);
    Z3_decl_kind decl_kind = Z3_get_decl_kind(fctx.z3_ctx, decl);
    if (decl_kind != Z3_OP_AND || Z3_get_app_num_args(fctx.z3_ctx, app) == 0) {
        *assertions = NULL;
        *n          = 0;
        return;
    }

    *n          = Z3_get_app_num_args(fctx.z3_ctx, app) - 1;
    *assertions = (Z3_ast*)malloc(sizeof(Z3_ast) * *n);

    unsigned i;
    for (i = 1; i < *n + 1; ++i) {
        Z3_ast v             = Z3_get_app_arg(fctx.z3_ctx, app, i);
        (*assertions)[i - 1] = v;
    }
}

static inline void dump_flip_info()
{
    fprintf(flip_info_file,
            "%ld," // input to state
            "%ld," // extended input to state
            "%ld," // interval analysis (brute force + range brute force + range
                   // brute force opt + simple math)
            "%ld," // gradient descent
            "%ld," // flips
            "%ld," // arithms
            "%ld," // interesting
            "%ld," // havoc
            "%ld," // multigoal
            "%ld"  // sat in seed
            ,
            fctx.stats.input_to_state, fctx.stats.input_to_state_ext,
            fctx.stats.brute_force + fctx.stats.range_brute_force +
                fctx.stats.range_brute_force_opt + fctx.stats.simple_math,
            fctx.stats.gradient_descend,
            fctx.stats.flip1 + fctx.stats.flip2 + fctx.stats.flip4 +
                fctx.stats.flip8 + fctx.stats.flip16 + fctx.stats.flip32 +
                fctx.stats.flip64,
            fctx.stats.arith8_sum + fctx.stats.arith8_sub +
                fctx.stats.arith16_sum_LE + fctx.stats.arith16_sum_BE +
                fctx.stats.arith16_sub_LE + fctx.stats.arith16_sub_BE +
                fctx.stats.arith32_sum_LE + fctx.stats.arith32_sum_BE +
                fctx.stats.arith32_sub_LE + fctx.stats.arith32_sub_BE +
                fctx.stats.arith64_sum_LE + fctx.stats.arith64_sum_BE +
                fctx.stats.arith64_sub_LE + fctx.stats.arith64_sub_BE,
            fctx.stats.int8 + fctx.stats.int16 + fctx.stats.int32 +
                fctx.stats.int64,
            fctx.stats.havoc, fctx.stats.multigoal, fctx.stats.sat_in_seed);
}

static inline void usage(char* filename)
{
    fprintf(stderr, "wrong argv. usage:\n%s query_filename seed [test_dir]\n",
            filename);
    exit(1);
}

int main(int argc, char* argv[])
{
    if (argc < 3)
        usage(argv[0]);

    char*     query_filename = argv[1];
    char*     seed_filename  = argv[2];
    char*     tests_dir      = argc > 3 ? argv[3] : NULL;
    Z3_config cfg            = Z3_mk_config();
    Z3_context           ctx = Z3_mk_context(cfg);
    unsigned char const* proof;
    unsigned long        proof_size;
    unsigned long        num_queries = 0, fuzzy_sat = 0;
    char                 var_name[128];
    Z3_sort              bsort = Z3_mk_bv_sort(ctx, 8);
    struct timeval       stop, start;
    double               elapsed_time = 0, cumulative_fuzzy = 0;
    unsigned int         i;
    int                  n;

#ifdef LOG_ON_FILE
    log_file = fopen(log_filename, "w");
    setvbuf(log_file, NULL, _IONBF, 0);
    flip_info_file = fopen(flip_info_filename, "w");
    setvbuf(flip_info_file, NULL, _IONBF, 0);
#endif

    z3fuzz_init(&fctx, ctx, seed_filename, tests_dir, NULL,
                FUZZY_SOLVER_TIMEOUT);

    pp_init();

    Z3_ast* str_symbols = (Z3_ast*)malloc(sizeof(Z3_ast) * fctx.n_symbols);
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

#ifdef LOG_ON_FILE
    fprintf(log_file, "time fuzzy,fuzzy res,time z3,z3 res\n");
#endif

    num_queries = Z3_ast_vector_size(ctx, queries);
    for (i = 0; i < num_queries; ++i) {
        pp_printf(0, 1, "query %ld/%ld", i + 1, num_queries);

        Z3_ast query = Z3_ast_vector_get(ctx, queries, i);
        query        = Z3_substitute(ctx, query, fctx.n_symbols, str_symbols,
                              fctx.symbols);
        Z3_ast   branch_condition = find_branch_condition(query);
        Z3_ast*  assertions;
        unsigned n_assertions;
        divide_query_in_assertions(query, &assertions, &n_assertions);

        int is_sat_fuzzy = 0;
        gettimeofday(&start, NULL);
        int j;
        for (j = 0; j < n_assertions; ++j) {
            assert(assertions[j] != NULL && "null assertion!");
            z3fuzz_notify_constraint(&fctx, assertions[j]);
        }

        if (z3fuzz_query_check_light(&fctx, query, branch_condition, &proof,
                                     &proof_size))
            is_sat_fuzzy = 1;

        gettimeofday(&stop, NULL);
        elapsed_time = compute_time_msec(&start, &stop);
        cumulative_fuzzy += elapsed_time;
        fuzzy_sat += is_sat_fuzzy;

#ifdef LOG_ON_FILE
        fprintf(log_file, "%.3lf,%s\n", elapsed_time,
                is_sat_fuzzy ? "sat" : "unknown");
#endif

        free(assertions);

        pp_printf(2, 1, "cumulative fuzzy  %.03lf msec", cumulative_fuzzy);
        pp_printf(3, 1, "sat fuzzy         %ld", fuzzy_sat);
    }

#ifdef LOG_ON_FILE
    dump_flip_info();
#endif

    pp_printf(2, 1, "cumulative fuzzy  %.03lf msec", cumulative_fuzzy);
    pp_printf(3, 1, "sat fuzzy         %ld", fuzzy_sat);
    pp_set_line(5);
    puts("");

    Z3_ast_vector_dec_ref(ctx, queries);
    free(str_symbols);
    z3fuzz_free(&fctx);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
    fclose(log_file);
    fclose(flip_info_file);
    return 0;
}
