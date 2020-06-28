#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>
#include "utility/pretty-print.h"
#include "z3-fuzzy.h"

#define Z3_SOLVER_TIMEOUT "10000"
#define FUZZY_SOLVER_TIMEOUT 1000

fuzzy_ctx_t fctx;
const char* log_filename = "fuzzy_z3.csv";
FILE*       log_file;

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
    Z3_set_param_value(cfg, "timeout", Z3_SOLVER_TIMEOUT);
    Z3_context           ctx = Z3_mk_context(cfg);
    unsigned char const* proof;
    unsigned long        proof_size;
    unsigned long        num_queries = 0, fuzzy_sat = 0, z3_sat = 0;
    char                 var_name[128];
    Z3_sort              bsort = Z3_mk_bv_sort(ctx, 8);
    struct timeval       stop, start;
    double       elapsed_time = 0, cumulative_fuzzy = 0, cumulative_z3 = 0;
    unsigned int i;
    int          n;

    pp_init();
    FILE* log_file = fopen(log_filename, "w");
    setvbuf(log_file, NULL, _IONBF, 0);

    z3fuzz_init(&fctx, ctx, seed_filename, tests_dir, NULL,
                FUZZY_SOLVER_TIMEOUT);

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

    fprintf(log_file, "time fuzzy,fuzzy res,time z3,z3 res\n");

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

        int is_sat_fuzzy  = 0;
        int is_sat_z3     = 0;
        int is_unknown_z3 = 0;

        pp_printf(6, 1, "running fuzzy...");
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
        free(assertions);

        fprintf(log_file, "%.3lf,%s,", elapsed_time,
                is_sat_fuzzy ? "sat" : "unknown");

        Z3_lbool  query_result;
        Z3_solver solver = Z3_mk_solver(ctx);
        Z3_solver_inc_ref(ctx, solver);

        pp_printf(6, 1, "running z3...");
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

        fprintf(log_file, "%.3lf,%s\n", elapsed_time,
                is_sat_z3 ? "sat" : (is_unknown_z3 ? "unknown" : "unsat"));

        pp_printf(1, 1, "cumulative z3     %.03lf msec", cumulative_z3);
        pp_printf(2, 1, "cumulative fuzzy  %.03lf msec", cumulative_fuzzy);
        pp_printf(3, 1, "sat fuzzy         %ld", fuzzy_sat);
        pp_printf(4, 1, "sat z3            %ld", z3_sat);
    }

    pp_printf(6, 1, "speedup   %.02lf x", cumulative_z3 / cumulative_fuzzy);
    pp_printf(7, 1, "detected  %ld / %ld", fuzzy_sat, z3_sat);
    puts("");
    Z3_ast_vector_dec_ref(ctx, queries);
    free(str_symbols);
    z3fuzz_free(&fctx);
    Z3_del_config(cfg);
    fclose(log_file);
    return 0;
}
