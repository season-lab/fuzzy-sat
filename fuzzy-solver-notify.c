#define FUZZY_SOURCE

#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>
#include "utility/pretty-print.h"
#include "z3-fuzzy.h"

#define BOLD(s) "\033[1m\033[37m" s "\033[0m"

#define CHECK_CONSISTENCY
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

static Z3_func_decl* fdecl_cache         = NULL;
static size_t        fdecl_cache_size    = 0;
static Z3_ast        byte_val_cache[256] = {0};

__attribute__((unused)) static uint64_t Z3_eval(Z3_context ctx, Z3_ast query,
                                                uint64_t* data,
                                                uint8_t*  symbols_sizes,
                                                size_t    size)
{
    uint64_t res;
    Z3_model z3_m = Z3_mk_model(ctx);
    Z3_model_inc_ref(ctx, z3_m);
    Z3_ast* z3_vals = (Z3_ast*)calloc(sizeof(Z3_ast), size);

    if (fdecl_cache == NULL) {
        fdecl_cache      = (Z3_func_decl*)calloc(sizeof(Z3_func_decl), size);
        fdecl_cache_size = size;
    } else if (fdecl_cache_size < size) {
        fdecl_cache =
            (Z3_func_decl*)realloc(fdecl_cache, size * sizeof(Z3_func_decl));
        size_t i;
        for (i = fdecl_cache_size; i < size; ++i)
            fdecl_cache[i] = 0;
        fdecl_cache_size = size;
    }

    unsigned i;
    for (i = 0; i < size; ++i) {
        Z3_ast e;
        if (symbols_sizes[i] == 8 && byte_val_cache[data[i]] != NULL)
            e = byte_val_cache[data[i] & 0xff];
        else {
            Z3_sort sort = Z3_mk_bv_sort(ctx, symbols_sizes[i]);
            e            = Z3_mk_unsigned_int64(ctx, data[i], sort);
            Z3_inc_ref(ctx, e);
            if (symbols_sizes[i] == 8)
                byte_val_cache[data[i] & 0xff] = e;
            else
                z3_vals[i] = e;
        }

        Z3_func_decl decl;
        if (fdecl_cache[i] != NULL)
            decl = fdecl_cache[i];
        else {
            Z3_sort   sort = Z3_mk_bv_sort(ctx, symbols_sizes[i]);
            Z3_symbol s    = Z3_mk_int_symbol(ctx, i);
            decl           = Z3_mk_func_decl(ctx, s, 0, NULL, sort);
            fdecl_cache[i] = decl;
        }

        Z3_add_const_interp(ctx, z3_m, decl, e);
    }

    // evaluate the query in the model
    Z3_ast  solution;
    Z3_bool successfulEval =
        Z3_model_eval(ctx, z3_m, query, Z3_TRUE, &solution);
    if (!successfulEval) {
        puts("Failed to evaluate model");
        exit(1);
    }

    Z3_model_dec_ref(ctx, z3_m);
    if (Z3_get_ast_kind(ctx, solution) == Z3_NUMERAL_AST) {
        Z3_bool successGet = Z3_get_numeral_uint64(ctx, solution, &res);
        if (successGet != Z3_TRUE) {
            puts("Z3_get_numeral_uint64() failed to get constant");
            exit(1);
        }
    } else {
        res = Z3_get_bool_value(ctx, solution) == Z3_L_TRUE ? 1UL : 0UL;
    }

    for (i = 0; i < size; ++i)
        if (z3_vals[i] != NULL)
            Z3_dec_ref(ctx, z3_vals[i]);
    free(z3_vals);

    return res;
}

static inline void print_status(unsigned long current_query,
                                unsigned long num_queries)
{

    memory_impact_stats_t m_stats;
    z3fuzz_get_mem_stats(&fctx, &m_stats);

    pp_printf(0, 4, BOLD("query") " %ld/%ld", current_query, num_queries);
    pp_print_string(
        1, 2,
        "o-------------------------------------------------------------o");
    pp_printf(2, 2, "| " BOLD("num eval:") "   %ld", fctx.stats.num_evaluate);
    pp_print_string(3, 2, "| ");
    pp_printf(4, 2, "| " BOLD("its:") "        %ld", fctx.stats.input_to_state);
    pp_printf(5, 2, "| " BOLD("sm:") "         %ld", fctx.stats.simple_math);
    pp_printf(6, 2, "| " BOLD("rbf:") "        %ld",
              fctx.stats.range_brute_force);
    pp_printf(7, 2, "| " BOLD("gd:") "         %ld",
              fctx.stats.gradient_descend);
    pp_printf(8, 2, "| " BOLD("bit flips:") "  %ld, %ld, %ld", fctx.stats.flip1,
              fctx.stats.flip2, fctx.stats.flip4);
    pp_printf(9, 2, "| " BOLD("arithms:") "    %ld",
              fctx.stats.arith8_sum + fctx.stats.arith8_sub +
                  fctx.stats.arith16_sum_LE + fctx.stats.arith16_sum_BE +
                  fctx.stats.arith16_sub_LE + fctx.stats.arith16_sub_BE +
                  fctx.stats.arith32_sum_LE + fctx.stats.arith32_sum_BE +
                  fctx.stats.arith32_sub_LE + fctx.stats.arith32_sub_BE +
                  fctx.stats.arith64_sum_LE + fctx.stats.arith64_sum_BE +
                  fctx.stats.arith64_sub_LE + fctx.stats.arith64_sub_BE);
    pp_printf(10, 2, "| " BOLD("multigoal:") "  %ld", fctx.stats.multigoal);
    pp_print_string(11, 2, "| ");
    pp_printf(12, 2, "| " BOLD("# confl:") "          %ld",
              fctx.stats.num_conflicting);
    pp_printf(13, 2, "| " BOLD("confl cache size:") " %ld",
              m_stats.conflicting_ast_size);
    pp_printf(14, 2, "| " BOLD("num timeouts:") "     %ld",
              fctx.stats.num_timeouts);
    pp_printf(15, 2, "| ");
    pp_printf(16, 2, "| " BOLD("avg eval time:") " %.03lf usec",
              fctx.stats.avg_time_for_eval);

    pp_printf(2, 30, BOLD("sat:") "        %ld (%ld) [%ld opt]",
              fctx.stats.num_sat, fctx.stats.sat_in_seed, fctx.stats.opt_sat);
    pp_print_string(2, 64, "|");
    pp_print_string(3, 64, "|");
    pp_printf(4, 30, BOLD("its ext:") "    %ld", fctx.stats.input_to_state_ext);
    pp_print_string(4, 64, "|");
    pp_printf(5, 30, BOLD("bf:") "         %ld", fctx.stats.brute_force);
    pp_print_string(5, 64, "|");
    pp_printf(6, 30, BOLD("rbf opt:") "    %ld",
              fctx.stats.range_brute_force_opt);
    pp_print_string(6, 64, "|");
    pp_printf(7, 30, BOLD("havoc:") "      %ld", fctx.stats.havoc);
    pp_print_string(7, 64, "|");
    pp_printf(8, 30, BOLD("byte flips:") " %ld, %ld, %ld, %ld",
              fctx.stats.flip8, fctx.stats.flip16, fctx.stats.flip32,
              fctx.stats.flip64);
    pp_print_string(8, 64, "|");
    pp_printf(9, 30, BOLD("ints:") "       %ld",
              fctx.stats.int8 + fctx.stats.int16 + fctx.stats.int32 +
                  fctx.stats.int64);
    pp_print_string(9, 64, "|");
    pp_printf(10, 30, BOLD("fallbacks:") "  %ld (%ld)si (%ld)nt",
              fctx.stats.conflicting_fallbacks,
              fctx.stats.conflicting_fallbacks_same_inputs,
              fctx.stats.conflicting_fallbacks_no_true);
    pp_print_string(10, 64, "|");
    pp_print_string(11, 64, "|");
    pp_printf(12, 30, BOLD("# univ def:") "          %ld",
              fctx.stats.num_univocally_defined);
    pp_print_string(12, 64, "|");
    pp_printf(13, 30, BOLD("ast info cache size:") " %ld",
              m_stats.ast_info_cache_size);
    pp_print_string(13, 64, "|");
    pp_printf(14, 30, BOLD("ast info cache hits:") " %ld",
              fctx.stats.ast_info_cache_hits);
    pp_print_string(14, 64, "|");
    pp_print_string(15, 64, "|");
    pp_print_string(16, 64, "|");

    pp_print_string(
        17, 2,
        "o-------------------------------------------------------------o");

    pp_set_col(0);
    pp_set_line(18);
}

static inline void print_report()
{
    printf("*** REPORT ***\n\n");
    printf("num_evaluate:          %ld\n", fctx.stats.num_evaluate);
    printf("num_sat:               %ld\n", fctx.stats.num_sat);
    printf("num_sat_opt:           %ld\n", fctx.stats.opt_sat);
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
    unsigned long        elapsed_time = 0, elapsed_time_fast_sat = 0,
                  elapsed_time_parsing = 0;
    unsigned int i;
    int          n;

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

    gettimeofday(&start, NULL);
    Z3_ast_vector queries =
        Z3_parse_smtlib2_file(ctx, query_filename, 0, 0, 0, 0, 0, 0);
    Z3_ast_vector_inc_ref(ctx, queries);
    gettimeofday(&stop, NULL);
    elapsed_time_parsing += compute_time_msec(&start, &stop);

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
#ifdef CHECK_CONSISTENCY
            testcase_t* curr_t    = &fctx.testcases.data[0];
            uint64_t*   tmp_proof = malloc(sizeof(uint64_t) * proof_size);
            for (j = 0; j < proof_size; ++j)
                tmp_proof[j] = proof[j];
            assert(Z3_eval(ctx, query, tmp_proof, curr_t->value_sizes,
                           proof_size) &&
                   "Invalid solution!");
            free(tmp_proof);
#endif
        } else
            gettimeofday(&stop, NULL);

        elapsed_time += compute_time_msec(&start, &stop);
        free(assertions);

#ifdef PRINT_STATUS
        print_status(i, num_queries);
#endif
    }

#ifdef PRINT_STATUS
    print_status(i, num_queries);
#else
    print_report();
#endif
    printf("\n"
           "num queries:      %lu\n"
           "fast sat queries: %lu\n"
           "elaps time:       %.3lf s\n"
           "elaps time sat:   %.3lf s\n"
           "elaps time + par: %.3lf s\n",
           num_queries, sat_queries, (double)elapsed_time / 1000,
           (double)elapsed_time_fast_sat / 1000,
           (double)(elapsed_time + elapsed_time_parsing) / 1000);

    Z3_ast_vector_dec_ref(ctx, queries);
    free(str_symbols);
    free(fdecl_cache);
    z3fuzz_free(&fctx);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
#ifdef DUMP_SAT_QUERIES
    fclose(sat_queries_file);
#endif
    return 0;
}
