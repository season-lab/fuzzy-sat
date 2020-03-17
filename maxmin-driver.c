#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>
#include "z3-fuzzy.h"
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
    fprintf(stderr, "wrong argv. usage:\n%s pi_filename bv_filename seed\n",
            filename);
    exit(1);
}

static inline void dump_proof(Z3_context ctx, Z3_model m,
                              char const* test_case_name)
{
    FILE*         fp;
    unsigned long num_symbols, i;
    Z3_sort       bsort = Z3_mk_bv_sort(ctx, 8);

    fp          = fopen(test_case_name, "w");
    num_symbols = Z3_model_get_num_consts(ctx, m);
    for (i = 0; i < num_symbols; ++i) {
        Z3_symbol s    = Z3_mk_int_symbol(ctx, i);
        Z3_ast    s_bv = Z3_mk_const(ctx, s, bsort);

        Z3_ast  solution;
        Z3_bool successfulEval =
            Z3_model_eval(ctx, m, s_bv,
                          /*model_completion=*/Z3_TRUE, &solution);
        assert(successfulEval && "Failed to evaluate model");

        int     solution_byte = 0;
        Z3_bool successGet = Z3_get_numeral_int(ctx, solution, &solution_byte);
        assert (successGet == Z3_TRUE);
        fwrite(&solution_byte, sizeof(char), 1, fp);
    }
    fclose(fp);
}

int main(int argc, char* argv[])
{
    if (argc < 3)
        usage(argv[0]);

    char*          pi_filename   = argv[1];
    char*          bv_filename   = argv[2];
    char*          seed_filename = argv[3];
    Z3_config      cfg           = Z3_mk_config();
    Z3_context     ctx           = Z3_mk_context(cfg);
    Z3_ast*        str_symbols;
    char           var_name[128];
    Z3_sort        bsort = Z3_mk_bv_sort(ctx, 8);
    struct timeval stop, start;
    unsigned long  elapsed_time_z3 = 0, elapsed_time_fast = 0;
    unsigned long  num_assert;
    unsigned int   i;
    int            n;

    z3fuzz_init(&fctx, ctx, seed_filename, NULL);

    str_symbols = (Z3_ast*)malloc(sizeof(Z3_ast) * fctx.n_symbols);
    for (i = 0; i < fctx.n_symbols; ++i) {
        n = snprintf(var_name, sizeof(var_name), "k!%u", i);
        assert(n > 0 && n < sizeof(var_name) && "symbol name too long");
        Z3_symbol s    = Z3_mk_string_symbol(ctx, var_name);
        Z3_ast    s_bv = Z3_mk_const(ctx, s, bsort);
        str_symbols[i] = s_bv;
    }

    Z3_ast_vector pi_vector =
        Z3_parse_smtlib2_file(ctx, pi_filename, 0, 0, 0, 0, 0, 0);
    Z3_ast_vector_inc_ref(ctx, pi_vector);

    num_assert = Z3_ast_vector_size(ctx, pi_vector);
    assert(num_assert > 0 && "empty pi");

    Z3_ast asserts[num_assert];
    for (i = 0; i < num_assert; ++i) {
        asserts[i] = Z3_ast_vector_get(ctx, pi_vector, i);
    }
    Z3_ast_vector_dec_ref(ctx, pi_vector);

    Z3_ast pi = Z3_mk_and(ctx, num_assert, asserts);
    pi = Z3_substitute(ctx, pi, fctx.n_symbols, str_symbols, fctx.symbols);
    puts("[+] PI loaded");

    Z3_ast_vector bv_asserts =
        Z3_parse_smtlib2_file(ctx, bv_filename, 0, 0, 0, 0, 0, 0);
    assert(Z3_ast_vector_size(ctx, bv_asserts) == 1 && "bv must be unique");

    // I can only parse asserts. So I assume something like (== BV whatever)
    Z3_ast bv_tmp     = Z3_ast_vector_get(ctx, bv_asserts, 0);
    Z3_app bv_tmp_app = Z3_to_app(ctx, bv_tmp);
    Z3_ast bv         = Z3_get_app_arg(ctx, bv_tmp_app, 0);
    bv = Z3_substitute(ctx, bv, fctx.n_symbols, str_symbols, fctx.symbols);
    puts("[+] BV loaded\n");

    gettimeofday(&start, NULL);
    unsigned char const* inputs;
    unsigned long max_val = z3fuzz_maximize(&fctx, pi, bv, &inputs);
    z3fuzz_dump_proof(&fctx, "tests/max_val.bin", inputs, fctx.n_symbols);

    unsigned long min_val = z3fuzz_minimize(&fctx, pi, bv, &inputs);
    z3fuzz_dump_proof(&fctx, "tests/min_val.bin", inputs, fctx.n_symbols);
    gettimeofday(&stop, NULL);
    elapsed_time_fast = compute_time_usec(&start, &stop);

    gettimeofday(&start, NULL);
    Z3_optimize opt;
    Z3_model    m;
    unsigned long max_val_z3 = 0;
    opt                      = Z3_mk_optimize(ctx);
    Z3_optimize_inc_ref(ctx, opt);
    Z3_optimize_assert(ctx, opt, pi);
    Z3_optimize_maximize(ctx, opt, bv);

    switch (Z3_optimize_check(ctx, opt, 0, NULL)) {
        case Z3_L_FALSE:
            printf("max false! \n");
            break;
        case Z3_L_UNDEF:
            printf("max unknown! \n");
            break;
        case Z3_L_TRUE:
            m = Z3_optimize_get_model(ctx, opt);
            Z3_model_inc_ref(ctx, m);
            dump_proof(ctx, m, "tests/max_val_z3.bin");

            Z3_ast  solution;
            Z3_bool successfulEval =
                Z3_model_eval(ctx, m, bv,
                              /*model_completion=*/Z3_TRUE, &solution);
            assert(successfulEval && "Failed to evaluate model");

            Z3_bool successGet = Z3_get_numeral_uint64(ctx, solution, &max_val_z3);
            assert(successGet && "Failed to get numeral int");

            Z3_model_dec_ref(ctx, m);
            break;
    }
    Z3_optimize_dec_ref(ctx, opt);

    unsigned long min_val_z3 = 0;
    opt                      = Z3_mk_optimize(ctx);
    Z3_optimize_inc_ref(ctx, opt);
    Z3_optimize_assert(ctx, opt, pi);
    Z3_optimize_minimize(ctx, opt, bv);

    switch (Z3_optimize_check(ctx, opt, 0, NULL)) {
        case Z3_L_FALSE:
            printf("max false! \n");
            break;
        case Z3_L_UNDEF:
            printf("max unknown! \n");
            break;
        case Z3_L_TRUE:
            m = Z3_optimize_get_model(ctx, opt);
            Z3_model_inc_ref(ctx, m);
            dump_proof(ctx, m, "tests/min_val_z3.bin");

            Z3_ast  solution;
            Z3_bool successfulEval =
                Z3_model_eval(ctx, m, bv,
                              /*model_completion=*/Z3_TRUE, &solution);
            assert(successfulEval && "Failed to evaluate model");

            Z3_bool successGet = Z3_get_numeral_uint64(ctx, solution, &min_val_z3);
            assert(successGet && "Failed to get numeral int");
            Z3_model_dec_ref(ctx, m);
            break;
    }
    Z3_optimize_dec_ref(ctx, opt);
    gettimeofday(&stop, NULL);
    elapsed_time_z3 = compute_time_usec(&start, &stop);

    printf("z3fuzz max_val:\t0x%lx\n", max_val);
    printf("z3fuzz min_val:\t0x%lx\n", min_val);
    printf("z3fuzz time:\t%ld usec\n", elapsed_time_fast);
    putchar('\n');
    printf("z3 max_val:\t0x%lx\n", max_val_z3);
    printf("z3 min_val:\t0x%lx\n", min_val_z3);
    printf("z3 time:\t%ld usec\n", elapsed_time_z3);

    z3fuzz_free(&fctx);

    return 0;
}
