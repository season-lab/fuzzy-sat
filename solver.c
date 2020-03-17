#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>
#include "utility/pretty-print.h"
#include <z3.h>
#define Z3_VERSION 487

#define SOLVER_TIMEOUT "10000" // 10 sec // 0

#define PRINT_STATUS
// #define PRINT_STATS_ON_FILE
// #define DUMP_SAT_QUERIES
// #define DUMP_UNKNOWN_QUERIES
#define DUMP_PROOFS
// #define EVAL_ONLY_BRANCH

static_assert(Z3_VERSION == 487, "This executable requires z3 4.8.7+");

const char* sat_queries_filename = "solver-sat-queries.smt2";
const char* unk_queries_filename = "solver-unknown-queries.smt2";

static inline void
print_stats_on_file(const char* query, unsigned long sat_queries,
                    double elapsed_time_sat, unsigned long unsat_queries,
                    double elapsed_time_unsat, unsigned long unknown_queries,
                    double elapsed_time_unknown, double elapsed_time)
{
    FILE* logfile = fopen("/tmp/z3fuzzy-log.csv", "w");
    fprintf(logfile, "%s;%ld;%ld;%.3lf;%ld;%.3lf;%ld;%.3lf;%.3lf\n", query,
            sat_queries + unsat_queries + unknown_queries, sat_queries,
            elapsed_time_sat, unsat_queries, elapsed_time_unsat,
            unknown_queries, elapsed_time_unknown, elapsed_time);
    fclose(logfile);
}

static inline void dump_proof(Z3_context ctx, Z3_model m,
                              char const* test_case_name)
{
    FILE*         fp;
    unsigned int  n;
    unsigned long num_symbols, i;
    char          var_name[128];
    Z3_sort       bsort = Z3_mk_bv_sort(ctx, 8);

    fp          = fopen(test_case_name, "w");
    num_symbols = Z3_model_get_num_consts(ctx, m);
    for (i = 0; i < num_symbols; ++i) {
        n = snprintf(var_name, sizeof(var_name), "k!%lu", i);
        assert(n > 0 && n < sizeof(var_name) && "symbol name too long");
        Z3_symbol s    = Z3_mk_string_symbol(ctx, var_name);
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

static inline Z3_ast find_branch_condition(Z3_context ctx, Z3_ast query)
{
    if (Z3_get_ast_kind(ctx, query) != Z3_APP_AST)
        return query;

    Z3_app       app       = Z3_to_app(ctx, query);
    Z3_func_decl decl      = Z3_get_app_decl(ctx, app);
    Z3_decl_kind decl_kind = Z3_get_decl_kind(ctx, decl);
    if (decl_kind != Z3_OP_AND)
        return query;

    return Z3_get_app_arg(ctx, app, 0);
}

static inline unsigned long compute_time_msec(struct timeval* start,
                                              struct timeval* end)
{
    return ((end->tv_sec - start->tv_sec) * 1000000 + end->tv_usec -
            start->tv_usec) /
           1000;
}

static inline void usage(char* filename)
{
    fprintf(stderr, "wrong argv. usage:\n%s query_filename\n", filename);
    exit(1);
}

int main(int argc, char* argv[])
{
    if (argc < 2)
        usage(argv[0]);

    char*     query_filename = argv[1];
    Z3_config cfg            = Z3_mk_config();
    Z3_set_param_value(cfg, "timeout", SOLVER_TIMEOUT);

    Z3_context    ctx = Z3_mk_context(cfg);
    Z3_solver     solver;
    unsigned long num_queries = 0, sat_queries = 0, unsat_queries = 0,
                  unknown_queries = 0;
    Z3_ast         query;
    Z3_lbool       query_result;
    struct timeval stop, start;
    unsigned long  elapsed_time = 0, elapsed_time_sat = 0,
                  elapsed_time_unsat = 0, elapsed_time_unk = 0;
    unsigned long elapsed_tmp = 0;
    unsigned int  i, j, n;
    char          var_name[128];

#ifdef PRINT_STATUS
    pp_init();
#endif

#ifdef DUMP_SAT_QUERIES
    FILE* sat_queries_file = fopen(sat_queries_filename, "w");
#endif
#ifdef DUMP_UNKNOWN_QUERIES
    FILE* unk_queries_file = fopen(unk_queries_filename, "w");
#endif

    Z3_ast_vector queries =
        Z3_parse_smtlib2_file(ctx, query_filename, 0, 0, 0, 0, 0, 0);
    Z3_ast_vector_inc_ref(ctx, queries);

    j           = 0;
    num_queries = Z3_ast_vector_size(ctx, queries);
    for (i = 0; i < num_queries; ++i) {

#ifdef PRINT_STATUS
        pp_printf(1, 1, "processing query %d/%ld", i, num_queries);
#endif

        query = Z3_ast_vector_get(ctx, queries, i);

        solver = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, solver);

        gettimeofday(&start, NULL);

#ifdef EVAL_ONLY_BRANCH
        Z3_solver_assert(ctx, solver, find_branch_condition(ctx, query));
#else
        Z3_solver_assert(ctx, solver, query);
#endif
        switch ((query_result = Z3_solver_check(ctx, solver))) {
            case Z3_L_FALSE:
                // printf("Query is UNSAT\n");
                unsat_queries += 1;
                gettimeofday(&stop, NULL);
                elapsed_time_unsat += compute_time_msec(&start, &stop);
                break;
            case Z3_L_UNDEF:
                /* Z3 failed to prove/disprove f. */
                unknown_queries += 1;
                gettimeofday(&stop, NULL);
                elapsed_time_unk += compute_time_msec(&start, &stop);
                break;
            case Z3_L_TRUE:
                // printf("Query is SAT\n");
                sat_queries += 1;
                gettimeofday(&stop, NULL);
                elapsed_time_sat += compute_time_msec(&start, &stop);
                break;
        }

        gettimeofday(&stop, NULL);
        elapsed_tmp = compute_time_msec(&start, &stop);
        elapsed_time += elapsed_tmp;

        if (query_result == Z3_L_TRUE) {
#ifdef DUMP_SAT_QUERIES
            fprintf(sat_queries_file, "(assert\n%s\n)\n",
                    Z3_ast_to_string(ctx, query));
#endif
#ifdef DUMP_PROOFS
            n = snprintf(var_name, sizeof(var_name), "tests/test_%02u", i);
            assert(n > 0 && n < sizeof(var_name) && "test case name too long");

            Z3_model m = Z3_solver_get_model(ctx, solver);
            Z3_model_inc_ref(ctx, m);
            dump_proof(ctx, m, var_name);
            Z3_model_dec_ref(ctx, m);
#endif
        } else if (query_result == Z3_L_UNDEF) {
#ifdef DUMP_UNKNOWN_QUERIES
            fprintf(unk_queries_file, "(assert\n%s\n)\n",
                    Z3_ast_to_string(ctx, query));
#endif
        }
        // printf("query %d: %lf s\n", j, (double)elapsed_tmp / 1000);
        j += 1;

        Z3_solver_dec_ref(ctx, solver);

#ifdef PRINT_STATUS
        pp_printf(2, 1, "sat queries      %ld", sat_queries);
        pp_printf(3, 1, "unsat queries    %ld", unsat_queries);
        pp_printf(4, 1, "unknown queries  %ld", unknown_queries);
#endif
    }

#ifdef PRINT_STATUS
    pp_set_line(5);
    pp_set_col(0);
#endif

    Z3_ast_vector_dec_ref(ctx, queries);
    printf("\n"
           "num queries:\t%lu\n"
           "sat queries:\t%lu\n"
           "elapsed time sat:\t%.3lf s\n"
           "unsat queries:\t%lu\n"
           "elapsed time unsat:\t%.3lf s\n"
           "unkn queries:\t%lu\n"
           "elapsed time unk:\t%.3lf s\n"
           "elapsed time:\t%.3lf s\n",
           num_queries, sat_queries, (double)elapsed_time_sat / 1000,
           unsat_queries, (double)elapsed_time_unsat / 1000, unknown_queries,
           (double)elapsed_time_unk / 1000, (double)elapsed_time / 1000);

#ifdef PRINT_STATS_ON_FILE
    print_stats_on_file(
        query_filename, sat_queries, (double)elapsed_time_sat / 1000,
        unsat_queries, (double)elapsed_time_unsat / 1000, unknown_queries,
        (double)elapsed_time_unk / 1000, (double)elapsed_time / 1000);
#endif

#ifdef DUMP_SAT_QUERIES
    fclose(sat_queries_file);
#endif
#ifdef DUMP_UNKNOWN_QUERIES
    fclose(unk_queries_file);
#endif

    Z3_del_config(cfg);
    return 0;
}