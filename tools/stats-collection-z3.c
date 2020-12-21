#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>
#include "pretty-print.h"
#include "z3-fuzzy.h"

#define LOG_ON_FILE
#define Z3_SOLVER_TIMEOUT "10000"

const char* log_filename = "z3_queries.csv";
FILE*       log_file;

static inline double compute_time_msec(struct timeval* start,
                                       struct timeval* end)
{
    return ((end->tv_sec - start->tv_sec) * 1000000 + end->tv_usec -
            start->tv_usec) /
           1000.0L;
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
    Z3_set_param_value(cfg, "timeout", Z3_SOLVER_TIMEOUT);
    Z3_context     ctx         = Z3_mk_context(cfg);
    unsigned long  num_queries = 0, z3_sat = 0;
    struct timeval stop, start;
    double         elapsed_time, cumulative_z3 = 0;
    unsigned int   i;

#ifdef LOG_ON_FILE
    log_file = fopen(log_filename, "w");
    setvbuf(log_file, NULL, _IONBF, 0);
#endif

    pp_init();

    Z3_ast_vector queries =
        Z3_parse_smtlib2_file(ctx, query_filename, 0, 0, 0, 0, 0, 0);
    Z3_ast_vector_inc_ref(ctx, queries);

#ifdef LOG_ON_FILE
    fprintf(log_file, "time z3,z3 res\n");
#endif

    num_queries = Z3_ast_vector_size(ctx, queries);
    for (i = 0; i < num_queries; ++i) {
        pp_printf(0, 1, "query %ld/%ld", i + 1, num_queries);

        Z3_ast query = Z3_ast_vector_get(ctx, queries, i);

        int is_sat_z3     = 0;
        int is_unknown_z3 = 0;

        Z3_lbool  query_result;
        Z3_solver solver = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, solver);

        gettimeofday(&start, NULL);
        Z3_solver_assert(ctx, solver, query);
        switch ((query_result = Z3_solver_check(ctx, solver))) {
            case Z3_L_FALSE:
                break;
            case Z3_L_UNDEF:
                is_unknown_z3 = 1;
                break;
            case Z3_L_TRUE:
                is_sat_z3 = 1;
                break;
        }

        gettimeofday(&stop, NULL);
        elapsed_time = compute_time_msec(&start, &stop);
        cumulative_z3 += elapsed_time;
        z3_sat += is_sat_z3;

        Z3_solver_dec_ref(ctx, solver);

#ifdef LOG_ON_FILE
        fprintf(log_file, "%.3lf,%s", elapsed_time,
                is_sat_z3 ? "sat" : (is_unknown_z3 ? "unknown" : "unsat"));
        fprintf(log_file, "\n");
#endif

        pp_printf(2, 1, "cumulative z3 %.03lf msec", cumulative_z3);
        pp_printf(3, 1, "sat z3        %ld", z3_sat);
    }

    pp_printf(2, 1, "cumulative z3 %.03lf msec", cumulative_z3);
    pp_printf(3, 1, "sat z3        %ld", z3_sat);
    pp_set_line(5);
    puts("");
    Z3_ast_vector_dec_ref(ctx, queries);
    Z3_del_config(cfg);
    Z3_del_context(ctx);
    fclose(log_file);
    return 0;
}