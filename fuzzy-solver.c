#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>
#include "utility/pretty-print.h"
#include "z3-fuzzy.h"
static_assert(Z3_VERSION == 487, "This executable requires z3 4.8.7+");

#define SOLVER_TIMEOUT "10000" // 10 sec // 0

#define PRINT_STATUS
// #define PRINT_SAT_IDX
// #define PRINT_STATS_ON_FILE
// #define DUMP_SAT_QUERIES
// #define DUMP_Z3_SAT_ONLY
// #define DUMP_PROOFS
// #define EVAL_ONLY_BRANCH
// #define Z3_FALLTHROUGH

fuzzy_ctx_t fctx;
const char* sat_queries_filename         = "fuzzy-sat-queries.smt2";
const char* sat_queries_only_z3_filename = "/tmp/sat-z3-only.smt2";

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

static inline void print_status(unsigned long current_query,
                                unsigned long num_queries,
                                unsigned long sat_queries_z3,
                                unsigned long unsat_queries_z3,
                                unsigned long unkn_queries_z3)
{
    pp_printf(0, 1, "query %ld/%ld", current_query, num_queries);
    pp_printf(1, 1, "num_evaluate:       %ld", fctx.stats.num_evaluate);
    pp_printf(2, 1, "num_sat:            %ld", fctx.stats.num_sat);
    pp_printf(3, 1, "reuse:              %ld", fctx.stats.reuse);
    pp_printf(4, 1, "input_to_state:     %ld", fctx.stats.input_to_state);
    pp_printf(5, 1, "input_to_state_ext: %ld", fctx.stats.input_to_state_ext);
    pp_printf(6, 1, "brute_force:        %ld", fctx.stats.brute_force);
    pp_printf(7, 1, "gradient_descend:   %ld", fctx.stats.gradient_descend);
    pp_printf(8, 1, "flip1:              %ld", fctx.stats.flip1);
    pp_printf(9, 1, "flip2:              %ld", fctx.stats.flip2);
    pp_printf(10, 1, "flip4:              %ld", fctx.stats.flip4);
    pp_printf(11, 1, "flip8:              %ld", fctx.stats.flip8);
    pp_printf(12, 1, "flip16:             %ld", fctx.stats.flip16);
    pp_printf(13, 1, "flip32:             %ld", fctx.stats.flip32);
    pp_printf(14, 1, "arith8_sum:         %ld", fctx.stats.arith8_sum);
    pp_printf(15, 1, "arith8_sub:         %ld", fctx.stats.arith8_sub);
    pp_printf(16, 1, "arith16_sum_LE:     %ld", fctx.stats.arith16_sum_LE);
    pp_printf(17, 1, "arith16_sum_BE:     %ld", fctx.stats.arith16_sum_BE);
    pp_printf(18, 1, "arith16_sub_LE:     %ld", fctx.stats.arith16_sub_LE);
    pp_printf(19, 1, "arith16_sub_BE:     %ld", fctx.stats.arith16_sub_BE);
    pp_printf(20, 1, "arith32_sum_LE:     %ld", fctx.stats.arith32_sum_LE);
    pp_printf(21, 1, "arith32_sum_BE:     %ld", fctx.stats.arith32_sum_BE);
    pp_printf(22, 1, "arith32_sub_LE:     %ld", fctx.stats.arith32_sub_LE);
    pp_printf(23, 1, "arith32_sub_BE:     %ld", fctx.stats.arith32_sub_BE);
    pp_printf(24, 1, "int8:               %ld", fctx.stats.int8);
    pp_printf(25, 1, "int16:              %ld", fctx.stats.int16);
    pp_printf(26, 1, "int32:              %ld", fctx.stats.int32);
    pp_printf(27, 1, "havoc:              %ld", fctx.stats.havoc);
#ifdef Z3_FALLTHROUGH
    pp_printf(33, 1, "sat z3:               %ld", sat_queries_z3);
    pp_printf(34, 1, "unsat z3:             %ld", unsat_queries_z3);
    pp_printf(35, 1, "unkn z3:              %ld", unkn_queries_z3);
#endif
    pp_set_col(0);
    pp_set_line(36);
}

static inline void
print_stats_on_file(const char* query_name, unsigned long num_queries,
                    unsigned long num_sat_fast, unsigned long num_sat_z3,
                    unsigned long num_unsat, unsigned long num_unkn,
                    double elapsed_time, double elapsed_time_fast_sat,
                    double elapsed_time_slow_sat, double elapsed_time_unsat,
                    double elapsed_time_unkn)
{
    FILE* logfile = fopen("/tmp/z3fuzzy-log.csv", "w");
    fprintf(logfile, "%s;%ld;%ld;flip data;\n", query_name, num_queries,
            fctx.stats.num_sat);
    fprintf(logfile, ";;;reuse;%ld\n", fctx.stats.reuse);
    fprintf(logfile, ";;;input_to_state;%ld\n", fctx.stats.input_to_state);
    fprintf(logfile, ";;;input_to_state_ext;%ld\n",
            fctx.stats.input_to_state_ext);
    fprintf(logfile, ";;;brute_force;%ld\n", fctx.stats.brute_force);
    fprintf(logfile, ";;;gradient_descend;%ld\n", fctx.stats.gradient_descend);
    fprintf(logfile, ";;;flip1;%ld\n", fctx.stats.flip1);
    fprintf(logfile, ";;;flip2;%ld\n", fctx.stats.flip2);
    fprintf(logfile, ";;;flip4;%ld\n", fctx.stats.flip4);
    fprintf(logfile, ";;;flip16;%ld\n", fctx.stats.flip16);
    fprintf(logfile, ";;;flip32;%ld\n", fctx.stats.flip32);
    fprintf(logfile, ";;;arith8_sum;%ld\n", fctx.stats.arith8_sum);
    fprintf(logfile, ";;;arith8_sub;%ld\n", fctx.stats.arith8_sub);
    fprintf(logfile, ";;;arith16_sum_LE;%ld\n", fctx.stats.arith16_sum_LE);
    fprintf(logfile, ";;;arith16_sum_BE;%ld\n", fctx.stats.arith16_sum_BE);
    fprintf(logfile, ";;;arith16_sub_LE;%ld\n", fctx.stats.arith16_sub_LE);
    fprintf(logfile, ";;;arith16_sub_BE;%ld\n", fctx.stats.arith16_sub_BE);
    fprintf(logfile, ";;;arith32_sum_LE;%ld\n", fctx.stats.arith32_sum_LE);
    fprintf(logfile, ";;;arith32_sum_BE;%ld\n", fctx.stats.arith32_sum_BE);
    fprintf(logfile, ";;;arith32_sub_LE;%ld\n", fctx.stats.arith32_sub_LE);
    fprintf(logfile, ";;;arith32_sub_BE;%ld\n", fctx.stats.arith32_sub_BE);
    fprintf(logfile, ";;;int8;%ld\n", fctx.stats.int8);
    fprintf(logfile, ";;;int16;%ld\n", fctx.stats.int16);
    fprintf(logfile, ";;;int32;%ld\n", fctx.stats.int32);
    fprintf(logfile, ";;;havoc;%ld\n", fctx.stats.havoc);
    fprintf(logfile, ";;;other data;\n");
    fprintf(logfile, ";;;elapsed time;%.3lf\n", elapsed_time);
    fprintf(logfile, ";;;elapsed time fast sat;%.3lf\n", elapsed_time_fast_sat);
#ifdef Z3_FALLTHROUGH
    fprintf(logfile, ";;;num sat fuzzy;%ld\n", num_sat_fast);
    fprintf(logfile, ";;;num sat z3;%ld\n", num_sat_z3);
    fprintf(logfile, ";;;elapsed time sat;%.3lf\n",
            elapsed_time_slow_sat + elapsed_time_fast_sat);
    fprintf(logfile, ";;;num unsat;%ld\n", num_unsat);
    fprintf(logfile, ";;;elapsed time unsat;%.3lf\n", elapsed_time_unsat);
    fprintf(logfile, ";;;num unknown;%ld\n", num_unkn);
    fprintf(logfile, ";;;elapsed time unknown;%.3lf\n", elapsed_time_unkn);
#endif
    fprintf(logfile, ";;;num evaluate;%ld\n", fctx.stats.num_evaluate);

    fclose(logfile);
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
    Z3_set_param_value(cfg, "timeout", SOLVER_TIMEOUT);
    Z3_context                            ctx = Z3_mk_context(cfg);
    unsigned char const*                  proof;
    unsigned long                         proof_size;
    __attribute__((unused)) unsigned long num_queries = 0, sat_queries = 0,
                                          sat_queries_z3   = 0,
                                          unsat_queries_z3 = 0,
                                          unkn_queries_z3  = 0;
    Z3_ast*                               str_symbols;
    char                                  var_name[128];
    Z3_sort                               bsort = Z3_mk_bv_sort(ctx, 8);
    struct timeval                        stop, start;
    __attribute__((unused)) unsigned long elapsed_time          = 0,
                                          elapsed_time_fast_sat = 0,
                                          elapsed_time_slow_sat = 0,
                                          elapsed_time_unsat    = 0,
                                          elapsed_time_unknown  = 0;
    unsigned int i;
    int          n;

#ifdef DUMP_Z3_SAT_ONLY
    FILE* sat_queries_z3_file = fopen(sat_queries_only_z3_filename, "w");
#endif
#ifdef DUMP_SAT_QUERIES
    FILE* sat_queries_file = fopen(sat_queries_filename, "w");
    setvbuf(sat_queries_file, NULL, _IONBF, 0);
#endif
    z3fuzz_init(&fctx, ctx, seed_filename, tests_dir, NULL);

#ifdef PRINT_STATUS
    pp_init();
#endif

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

#ifdef PRINT_SAT_IDX
    FILE* log_idx_sat = fopen("/tmp/idx_sat.csv", "w");
#endif

    num_queries = Z3_ast_vector_size(ctx, queries);
    for (i = 0; i < num_queries; ++i) {
        Z3_ast query = Z3_ast_vector_get(ctx, queries, i);
        query        = Z3_substitute(ctx, query, fctx.n_symbols, str_symbols,
                              fctx.symbols);
        __attribute__((unused)) Z3_ast branch_condition =
            find_branch_condition(query);

#ifdef EVAL_ONLY_BRANCH
        query = branch_condition;
#endif
        gettimeofday(&start, NULL);
        if (z3fuzz_query_check_light(&fctx, query, find_branch_condition(query),
                                     &proof, &proof_size)) {
            sat_queries += 1;
            gettimeofday(&stop, NULL);
            elapsed_time_fast_sat += compute_time_msec(&start, &stop);

#ifdef PRINT_SAT_IDX
            fprintf(log_idx_sat, "%u ; SAT\n", i);
#endif
#ifdef DUMP_SAT_QUERIES
            fprintf(sat_queries_file, "(assert\n%s\n)\n",
                    Z3_ast_to_string(ctx, query));
#endif
#ifdef DUMP_PROOFS
            n = snprintf(var_name, sizeof(var_name), "tests/test_%02u", i);
            assert(n > 0 && n < sizeof(var_name) && "test case name too long");
            z3fuzz_dump_proof(&fctx, var_name, proof, proof_size);
#endif
        } else {
            unsat_queries_z3++;
            gettimeofday(&stop, NULL);
            elapsed_time_unsat += compute_time_msec(&start, &stop);
#ifdef PRINT_SAT_IDX
            fprintf(log_idx_sat, "%u ; UNSAT\n", i);
#endif
#ifdef Z3_FALLTHROUGH
            Z3_solver solver = Z3_mk_solver(ctx);
            Z3_solver_inc_ref(ctx, solver);

#ifdef EVAL_ONLY_BRANCH
            Z3_solver_assert(ctx, solver, find_branch_condition(ctx, query));
#else
            Z3_solver_assert(ctx, solver, query);
#endif
            Z3_lbool query_result;
            switch ((query_result = Z3_solver_check(ctx, solver))) {
                case Z3_L_FALSE:
                    // printf("Query is UNSAT\n");
                    unsat_queries_z3 += 1;
                    gettimeofday(&stop, NULL);
                    elapsed_time_unsat += compute_time_msec(&start, &stop);
                    break;
                case Z3_L_UNDEF:
                    /* Z3 failed to prove/disprove f. */
                    unkn_queries_z3 += 1;
                    gettimeofday(&stop, NULL);
                    elapsed_time_unknown += compute_time_msec(&start, &stop);
                    break;
                case Z3_L_TRUE:
                    // printf("Query is SAT\n");
                    sat_queries_z3 += 1;
                    gettimeofday(&stop, NULL);
                    elapsed_time_slow_sat += compute_time_msec(&start, &stop);
#ifdef DUMP_Z3_SAT_ONLY
                    fprintf(sat_queries_z3_file, "(assert\n%s\n)\n",
                            Z3_ast_to_string(ctx, query));
#endif
                    break;
            }

            if (query_result == Z3_L_TRUE) {
#ifdef DUMP_SAT_QUERIES
                fprintf(sat_queries_file, "(assert\n%s\n)\n",
                        Z3_ast_to_string(ctx, query));
#endif
#ifdef DUMP_PROOFS
                n = snprintf(var_name, sizeof(var_name), "tests/test_%02u", i);
                assert(n > 0 && n < sizeof(var_name) &&
                       "test case name too long");

                Z3_model m = Z3_solver_get_model(ctx, solver);
                Z3_model_inc_ref(ctx, m);
                dump_proof(ctx, m, var_name);
                Z3_model_dec_ref(ctx, m);
#endif
            }

            Z3_solver_dec_ref(ctx, solver);
        }
#else
        }
        gettimeofday(&stop, NULL);
#endif

        elapsed_time += compute_time_msec(&start, &stop);

#ifdef PRINT_STATUS
        print_status(i, num_queries, sat_queries_z3, unsat_queries_z3,
                     unkn_queries_z3);
#endif
    }

#ifdef PRINT_STATS_ON_FILE
    print_stats_on_file(
        query_filename, num_queries, sat_queries, sat_queries_z3,
        unsat_queries_z3, unkn_queries_z3, (double)elapsed_time / 1000,
        (double)elapsed_time_fast_sat / 1000,
        (double)elapsed_time_slow_sat / 1000, (double)elapsed_time_unsat / 1000,
        (double)elapsed_time_unknown / 1000);
#endif
#ifdef PRINT_SAT_IDX
    fclose(log_idx_sat);
#endif
    printf("\n"
           "num queries:\t%lu\n"
           "fast sat queries:\t%lu\n"
           "elaps time:\t%.3lf s\n"
           "elaps time sat:\t%.3lf s\n",
           num_queries, sat_queries, (double)elapsed_time / 1000,
           (double)elapsed_time_fast_sat / 1000);
#ifdef Z3_FALLTHROUGH
    printf("slow z3 sat:\t%lu\n"
           "slow z3 unsat:\t%lu\n"
           "slow z3 unkn:\t%lu\n"
           "elaps time sat:\t%.3lf s\n"
           "elaps time unsat:\t%.3lf s\n"
           "elaps time unkn:\t%.3lf s\n",
           sat_queries_z3, unsat_queries_z3, unkn_queries_z3,
           (double)elapsed_time_slow_sat / 1000,
           (double)elapsed_time_unsat / 1000,
           (double)elapsed_time_unknown / 1000);
#endif

    printf("elaps time unsat:\t%.3lf s\n"
           "num unsat:\t%lu\n",
           (double)elapsed_time_unsat / 1000, unsat_queries_z3);

    Z3_ast_vector_dec_ref(ctx, queries);
    free(str_symbols);
    z3fuzz_free(&fctx);
    Z3_del_config(cfg);
#ifdef DUMP_SAT_QUERIES
    fclose(sat_queries_file);
#endif
#ifdef DUMP_Z3_SAT_ONLY
    fclose(sat_queries_z3_file);
#endif
    return 0;
}
