#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <z3.h>
#include "utility/pretty-print.h"
#include "z3-fuzzy.h"

#define USE_PP

unsigned char* inputs     = NULL;
unsigned long  num_inputs = 0;
unsigned       total      = 0;
unsigned       current    = 0;
fuzzy_ctx_t    fctx;

void debug_eval(Z3_context ctx, Z3_ast expr)
{
    switch (Z3_get_ast_kind(ctx, expr)) {
        case Z3_APP_AST: {
            Z3_app   app      = Z3_to_app(ctx, expr);
            unsigned num_args = Z3_get_app_num_args(ctx, app);

            unsigned i;
            for (i = 0; i < num_args; ++i) {
                Z3_ast child = Z3_get_app_arg(ctx, app, i);
                debug_eval(ctx, child);
            }

            Z3_sort expr_sort = Z3_get_sort(ctx, expr);
            if (Z3_get_sort_kind(ctx, expr_sort) == Z3_BV_SORT &&
                Z3_get_bv_sort_size(ctx, expr_sort) > 64)
                break;

            // z3
            unsigned long res_z3 = z3fuzz_evaluate_expression_z3(
                &fctx, expr, fctx.testcases.data[0].z3_bytes);

            // fuzzy
            unsigned long res_fuzzy = z3fuzz_evaluate_expression(
                &fctx, expr, fctx.testcases.data[0].bytes);

            if (res_fuzzy != res_z3) {
                printf("different evaluate\n"
                       "fuzzy: 0x%lx\n"
                       "z3: 0x%lx\n\n"
                       "%s\n",
                       res_fuzzy, res_z3, Z3_ast_to_string(ctx, expr));
                exit(1);
            }
            break;
        }
        case Z3_NUMERAL_AST: {
            break;
        }
        default: {
            assert(0 && "z3_jit_eval() unknown ast_kind");
        }
    }
    current++;

#ifdef USE_PP
    pp_printf(0, 1, "%u / %u", current, total);
    pp_set_line(3);
#endif
}

unsigned count_apps(Z3_context ctx, Z3_ast expr)
{
    unsigned counter = 0;
    switch (Z3_get_ast_kind(ctx, expr)) {
        case Z3_APP_AST: {
            Z3_app   app      = Z3_to_app(ctx, expr);
            unsigned num_args = Z3_get_app_num_args(ctx, app);

            counter = 1;
            unsigned i;
            for (i = 0; i < num_args; ++i) {
                Z3_ast child = Z3_get_app_arg(ctx, app, i);
                counter += count_apps(ctx, child);
            }
            break;
        }
        case Z3_NUMERAL_AST: {
            break;
        }
        default: {
            assert(0 && "z3_jit_eval() unknown ast_kind");
        }
    }
    return counter;
}

static inline void usage(char* filename)
{
    fprintf(stderr, "wrong argv. usage:\n%s query_filename seed\n", filename);
    exit(1);
}

static inline void init_input_data(char* filename)
{
    FILE*         fp = fopen(filename, "r");
    int           res, i = 0;
    unsigned char c;

    assert(fp != NULL && "fopen() failed");

    fseek(fp, 0L, SEEK_END);
    num_inputs = ftell(fp);
    fseek(fp, 0L, SEEK_SET);
    inputs = (unsigned char*)malloc(sizeof(unsigned char) * num_inputs);
    while (1) {
        res = fread(&c, sizeof(char), 1, fp);
        if (res != 1)
            break;
        inputs[i] = c;
        i++;
    }
    fclose(fp);
}

int main(int argc, char** argv)
{

    if (argc < 3)
        usage(argv[0]);

    char*      query_filename = argv[1];
    char*      seed_filename  = argv[2];
    Z3_config  cfg            = Z3_mk_config();
    Z3_context ctx            = Z3_mk_context(cfg);
    char       var_name[128];

    init_input_data(seed_filename);

    Z3_ast*  str_symbols = (Z3_ast*)malloc(sizeof(Z3_ast) * num_inputs);
    Z3_ast*  int_symbols = (Z3_ast*)malloc(sizeof(Z3_ast) * num_inputs);
    Z3_sort  bsort       = Z3_mk_bv_sort(ctx, 8);
    unsigned i;
    for (i = 0; i < num_inputs; ++i) {
        int n = snprintf(var_name, sizeof(var_name), "k!%u", i);
        assert(n > 0 && n < sizeof(var_name) && "symbol name too long");
        Z3_symbol s    = Z3_mk_string_symbol(ctx, var_name);
        Z3_ast    s_bv = Z3_mk_const(ctx, s, bsort);
        str_symbols[i] = s_bv;
        s              = Z3_mk_int_symbol(ctx, i);
        s_bv           = Z3_mk_const(ctx, s, bsort);
        int_symbols[i] = s_bv;
    }

    Z3_ast_vector queries =
        Z3_parse_smtlib2_file(ctx, query_filename, 0, 0, 0, 0, 0, 0);
    Z3_ast_vector_inc_ref(ctx, queries);
    unsigned num_queries = Z3_ast_vector_size(ctx, queries);
    assert(num_queries == 1 && "only one query is allowed");

    Z3_ast bv_tmp = Z3_ast_vector_get(ctx, queries, 0);
    Z3_ast_vector_dec_ref(ctx, queries);

    Z3_ast bv = bv_tmp;
    bv        = Z3_substitute(ctx, bv, num_inputs, str_symbols, int_symbols);
    puts("[+] BV loaded");

    z3fuzz_init(&fctx, ctx, seed_filename, NULL);
    puts("[+] FCTX initialized");

    pp_init();
    total = count_apps(ctx, bv);
    puts("[+] PP initialized");

    debug_eval(ctx, bv);

    z3fuzz_free(&fctx);
    return 0;
}
