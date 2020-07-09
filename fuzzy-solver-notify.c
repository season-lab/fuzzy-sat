#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>
#include "utility/pretty-print.h"
#include "z3-fuzzy.h"

#define PRINT_STATUS
// #define DUMP_PROOFS
// #define DUMP_SAT_QUERIES
#define TIMEOUT 1000

fuzzy_ctx_t fctx;
const char* sat_queries_filename = "query_db/SAT/fuzzy-sat-queries.smt2";

static inline unsigned long compute_time_msec(struct timeval* start,
                                              struct timeval* end)
{
    return ((end->tv_sec - start->tv_sec) * 1000000 + end->tv_usec -
            start->tv_usec) /
           1000;
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

static inline void print_status(unsigned long current_query,
                                unsigned long num_queries)
{
    pp_printf(0, 1, "query %ld/%ld", current_query, num_queries);
    pp_printf(1, 1, "num_evaluate:          %ld", fctx.stats.num_evaluate);
    pp_printf(2, 1, "num_sat:               %ld", fctx.stats.num_sat);
    pp_printf(3, 1, "reuse:                 %ld", fctx.stats.reuse);
    pp_printf(4, 1, "input_to_state:        %ld", fctx.stats.input_to_state);
    pp_printf(5, 1, "simple_math:           %ld", fctx.stats.simple_math);
    pp_printf(6, 1, "input_to_state_ext:    %ld",
              fctx.stats.input_to_state_ext);
    pp_printf(7, 1, "brute_force:           %ld", fctx.stats.brute_force);
    pp_printf(8, 1, "range_brute_force:     %ld", fctx.stats.range_brute_force);
    pp_printf(9, 1, "range_brute_force_opt: %ld",
              fctx.stats.range_brute_force_opt);
    pp_printf(10, 1, "gradient_descend:      %ld", fctx.stats.gradient_descend);
    pp_printf(11, 1, "flip1:                 %ld", fctx.stats.flip1);
    pp_printf(12, 1, "flip2:                 %ld", fctx.stats.flip2);
    pp_printf(13, 1, "flip4:                 %ld", fctx.stats.flip4);
    pp_printf(14, 1, "flip8:                 %ld", fctx.stats.flip8);
    pp_printf(15, 1, "flip16:                %ld", fctx.stats.flip16);
    pp_printf(16, 1, "flip32:                %ld", fctx.stats.flip32);
    pp_printf(17, 1, "flip64:                %ld", fctx.stats.flip64);
    pp_printf(18, 1, "arith8_sum:            %ld", fctx.stats.arith8_sum);
    pp_printf(19, 1, "arith8_sub:            %ld", fctx.stats.arith8_sub);
    pp_printf(20, 1, "arith16_sum_LE:        %ld", fctx.stats.arith16_sum_LE);
    pp_printf(21, 1, "arith16_sum_BE:        %ld", fctx.stats.arith16_sum_BE);
    pp_printf(22, 1, "arith16_sub_LE:        %ld", fctx.stats.arith16_sub_LE);
    pp_printf(23, 1, "arith16_sub_BE:        %ld", fctx.stats.arith16_sub_BE);
    pp_printf(24, 1, "arith32_sum_LE:        %ld", fctx.stats.arith32_sum_LE);
    pp_printf(25, 1, "arith32_sum_BE:        %ld", fctx.stats.arith32_sum_BE);
    pp_printf(26, 1, "arith32_sub_LE:        %ld", fctx.stats.arith32_sub_LE);
    pp_printf(27, 1, "arith32_sub_BE:        %ld", fctx.stats.arith32_sub_BE);
    pp_printf(28, 1, "arith64_sum_LE:        %ld", fctx.stats.arith64_sum_LE);
    pp_printf(29, 1, "arith64_sum_BE:        %ld", fctx.stats.arith64_sum_BE);
    pp_printf(30, 1, "arith64_sub_LE:        %ld", fctx.stats.arith64_sub_LE);
    pp_printf(31, 1, "arith64_sub_BE:        %ld", fctx.stats.arith64_sub_BE);
    pp_printf(32, 1, "int8:                  %ld", fctx.stats.int8);
    pp_printf(33, 1, "int16:                 %ld", fctx.stats.int16);
    pp_printf(34, 1, "int32:                 %ld", fctx.stats.int32);
    pp_printf(35, 1, "int64:                 %ld", fctx.stats.int64);
    pp_printf(36, 1, "havoc:                 %ld", fctx.stats.havoc);
    pp_printf(37, 1, "multigoal:             %ld", fctx.stats.multigoal);
    pp_printf(38, 1, "sat_in_seed:           %ld", fctx.stats.sat_in_seed);
    pp_printf(39, 1, "ast_info_cache_hits:   %ld",
              fctx.stats.ast_info_cache_hits);
    pp_printf(40, 1, "num_univ_defined:      %ld",
              fctx.stats.num_univocally_defined);
    pp_printf(41, 1, "num_conflicting:       %ld", fctx.stats.num_conflicting);
    pp_printf(42, 1, "confl_fallbacks:       %ld",
              fctx.stats.conflicting_fallbacks);
    pp_printf(43, 1, "confl_fall_noinp:      %ld",
              fctx.stats.conflicting_fallbacks_same_inputs);
    pp_printf(44, 1, "confl_fall_notrue:     %ld",
              fctx.stats.conflicting_fallbacks_no_true);
    pp_printf(45, 1, "num_timeouts:          %ld", fctx.stats.num_timeouts);
    pp_set_col(0);
    pp_set_line(47);
}

static inline void print_report()
{
    printf("*** REPORT ***\n\n");
    printf("num_evaluate:          %ld\n", fctx.stats.num_evaluate);
    printf("num_sat:               %ld\n", fctx.stats.num_sat);
    printf("reuse:                 %ld\n", fctx.stats.reuse);
    printf("input_to_state:        %ld\n", fctx.stats.input_to_state);
    printf("simple_math:           %ld\n", fctx.stats.simple_math);
    printf("input_to_state_ext:    %ld\n", fctx.stats.input_to_state_ext);
    printf("brute_force:           %ld\n", fctx.stats.brute_force);
    printf("range_brute_force:     %ld\n", fctx.stats.range_brute_force);
    printf("range_brute_force_opt: %ld\n", fctx.stats.range_brute_force_opt);
    printf("gradient_descend:      %ld\n", fctx.stats.gradient_descend);
    printf("flip1:                 %ld\n", fctx.stats.flip1);
    printf("flip2:                 %ld\n", fctx.stats.flip2);
    printf("flip4:                 %ld\n", fctx.stats.flip4);
    printf("flip8:                 %ld\n", fctx.stats.flip8);
    printf("flip16:                %ld\n", fctx.stats.flip16);
    printf("flip32:                %ld\n", fctx.stats.flip32);
    printf("flip64:                %ld\n", fctx.stats.flip64);
    printf("arith8_sum:            %ld\n", fctx.stats.arith8_sum);
    printf("arith8_sub:            %ld\n", fctx.stats.arith8_sub);
    printf("arith16_sum_LE:        %ld\n", fctx.stats.arith16_sum_LE);
    printf("arith16_sum_BE:        %ld\n", fctx.stats.arith16_sum_BE);
    printf("arith16_sub_LE:        %ld\n", fctx.stats.arith16_sub_LE);
    printf("arith16_sub_BE:        %ld\n", fctx.stats.arith16_sub_BE);
    printf("arith32_sum_LE:        %ld\n", fctx.stats.arith32_sum_LE);
    printf("arith32_sum_BE:        %ld\n", fctx.stats.arith32_sum_BE);
    printf("arith32_sub_LE:        %ld\n", fctx.stats.arith32_sub_LE);
    printf("arith32_sub_BE:        %ld\n", fctx.stats.arith32_sub_BE);
    printf("arith64_sum_LE:        %ld\n", fctx.stats.arith64_sum_LE);
    printf("arith64_sum_BE:        %ld\n", fctx.stats.arith64_sum_BE);
    printf("arith64_sub_LE:        %ld\n", fctx.stats.arith64_sub_LE);
    printf("arith64_sub_BE:        %ld\n", fctx.stats.arith64_sub_BE);
    printf("int8:                  %ld\n", fctx.stats.int8);
    printf("int16:                 %ld\n", fctx.stats.int16);
    printf("int32:                 %ld\n", fctx.stats.int32);
    printf("int64:                 %ld\n", fctx.stats.int64);
    printf("havoc:                 %ld\n", fctx.stats.havoc);
    printf("multigoal:             %ld\n", fctx.stats.multigoal);
    printf("sat_in_seed:           %ld\n", fctx.stats.sat_in_seed);
    printf("num_timeouts:          %ld\n", fctx.stats.num_timeouts);
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

    char*                query_filename = argv[1];
    char*                seed_filename  = argv[2];
    char*                tests_dir      = argc > 3 ? argv[3] : NULL;
    Z3_config            cfg            = Z3_mk_config();
    Z3_context           ctx            = Z3_mk_context(cfg);
    unsigned char const* proof;
    unsigned long        proof_size;
    unsigned long        num_queries = 0, sat_queries = 0;
    char                 var_name[128];
    Z3_sort              bsort = Z3_mk_bv_sort(ctx, 8);
    struct timeval       stop, start;
    unsigned long        elapsed_time = 0, elapsed_time_fast_sat = 0;
    unsigned int         i;
    int                  n;

    z3fuzz_init(&fctx, ctx, seed_filename, tests_dir, NULL, TIMEOUT);
#ifdef DUMP_SAT_QUERIES
    FILE* sat_queries_file = fopen(sat_queries_filename, "w");
    setvbuf(sat_queries_file, NULL, _IONBF, 0);
#endif

#ifdef PRINT_STATUS
    pp_init();
#endif

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

    num_queries = Z3_ast_vector_size(ctx, queries);
    for (i = 0; i < num_queries; ++i) {
        Z3_ast query = Z3_ast_vector_get(ctx, queries, i);
        query        = Z3_substitute(ctx, query, fctx.n_symbols, str_symbols,
                              fctx.symbols);
        Z3_ast   branch_condition = find_branch_condition(query);
        Z3_ast*  assertions;
        unsigned n_assertions;
        divide_query_in_assertions(query, &assertions, &n_assertions);

        gettimeofday(&start, NULL);
        int j;
        for (j = 0; j < n_assertions; ++j) {
            assert(assertions[j] != NULL && "null assertion!");
            z3fuzz_notify_constraint(&fctx, assertions[j]);
        }

        if (z3fuzz_query_check_light(&fctx, query, branch_condition, &proof,
                                     &proof_size)) {
            sat_queries += 1;
            gettimeofday(&stop, NULL);
            elapsed_time_fast_sat += compute_time_msec(&start, &stop);
#ifdef DUMP_PROOFS
            n = snprintf(var_name, sizeof(var_name), "tests/test_%02u", i);
            assert(n > 0 && n < sizeof(var_name) && "test case name too long");
            z3fuzz_dump_proof(&fctx, var_name, proof, proof_size);
#endif
#ifdef DUMP_SAT_QUERIES
            fprintf(sat_queries_file, "(assert\n%s\n)\n",
                    Z3_ast_to_string(ctx, query));
#endif
        } else
            gettimeofday(&stop, NULL);

        elapsed_time += compute_time_msec(&start, &stop);
        free(assertions);

#ifdef PRINT_STATUS
        print_status(i, num_queries);
#endif
    }

#ifndef PRINT_STATUS
    print_report();
#endif
    printf("\n"
           "num queries:      %lu\n"
           "fast sat queries: %lu\n"
           "elaps time:       %.3lf s\n"
           "elaps time sat:   %.3lf s\n",
           num_queries, sat_queries, (double)elapsed_time / 1000,
           (double)elapsed_time_fast_sat / 1000);

    Z3_ast_vector_dec_ref(ctx, queries);
    free(str_symbols);
    z3fuzz_free(&fctx);
    Z3_del_config(cfg);
#ifdef DUMP_SAT_QUERIES
    fclose(sat_queries_file);
#endif
    return 0;
}
