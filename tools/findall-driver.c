#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>
#include "z3-fuzzy.h"

#define NUM_ITERATIONS 1000
#define TIMEOUT 1000

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

static fuzzy_findall_res_t findall_callback(const unsigned char* out_bytes,
                                             unsigned long        out_bytes_len,
                                             unsigned long        val)
{
    printf("> found value 0x%016lx\n", val);
    return Z3FUZZ_GIVE_NEXT;
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
    unsigned long  elapsed_time = 0;
    unsigned long  num_assert;
    unsigned int   i;
    int            n;

    z3fuzz_init(&fctx, ctx, seed_filename, NULL, NULL, TIMEOUT);

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
    Z3_ast_vector_inc_ref(ctx, bv_asserts);
    assert(Z3_ast_vector_size(ctx, bv_asserts) == 1 && "bv must be unique");

    // I can only parse asserts. So I assume something like (== BV whatever)
    Z3_ast bv_tmp     = Z3_ast_vector_get(ctx, bv_asserts, 0);
    Z3_app bv_tmp_app = Z3_to_app(ctx, bv_tmp);
    Z3_ast bv         = Z3_get_app_arg(ctx, bv_tmp_app, 0);
    bv = Z3_substitute(ctx, bv, fctx.n_symbols, str_symbols, fctx.symbols);
    Z3_ast_vector_dec_ref(ctx, bv_asserts);
    puts("[+] BV loaded\n");

    gettimeofday(&start, NULL);

    puts("-- FINDALL --");
    z3fuzz_find_all_values(&fctx, bv, pi, findall_callback);
    puts("-- FINDALL GD MIN --");
    z3fuzz_find_all_values_gd(&fctx, bv, pi, 1, findall_callback);
    puts("-- FINDALL GD MAX --");
    z3fuzz_find_all_values_gd(&fctx, bv, pi, 0, findall_callback);
    puts("--------------------");

    gettimeofday(&stop, NULL);
    elapsed_time = compute_time_usec(&start, &stop);
    printf("elapsed time: %.03Lf msec\n", elapsed_time / 1000.0l);

    z3fuzz_free(&fctx);
    free(str_symbols);
    Z3_del_config(cfg);
    return 0;
}
