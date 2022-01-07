#ifndef Z3_FUZZY_H
#define Z3_FUZZY_H

#ifdef FUZZY_SOURCE
#include "testcase-list.h"
#endif

#include <z3.h>

typedef enum fuzzy_findall_res_t {
    Z3FUZZ_GIVE_NEXT,
    Z3FUZZ_STOP,
    Z3FUZZ_JUST_LAST
} fuzzy_findall_res_t;

typedef struct fuzzy_stats_t {
    unsigned long num_evaluate;
    unsigned long aggressive_opt_evaluate;
    unsigned long num_sat;
    unsigned long opt_sat;
    unsigned long reuse;
    unsigned long input_to_state;
    unsigned long simple_math;
    unsigned long input_to_state_ext;
    unsigned long brute_force;
    unsigned long range_brute_force;
    unsigned long range_brute_force_opt;
    unsigned long gradient_descend;
    unsigned long flip1;
    unsigned long flip2;
    unsigned long flip4;
    unsigned long flip8;
    unsigned long arith8_sum;
    unsigned long arith8_sub;
    unsigned long int8;
    unsigned long flip16;
    unsigned long arith16_sum_LE;
    unsigned long arith16_sum_BE;
    unsigned long arith16_sub_LE;
    unsigned long arith16_sub_BE;
    unsigned long int16;
    unsigned long flip32;
    unsigned long arith32_sum_LE;
    unsigned long arith32_sum_BE;
    unsigned long arith32_sub_LE;
    unsigned long arith32_sub_BE;
    unsigned long int32;
    unsigned long flip64;
    unsigned long arith64_sum_LE;
    unsigned long arith64_sum_BE;
    unsigned long arith64_sub_LE;
    unsigned long arith64_sub_BE;
    unsigned long int64;
    unsigned long havoc;
    unsigned long multigoal;
    unsigned long sat_in_seed;
    unsigned long num_univocally_defined;
    unsigned long num_range_constraints;
    unsigned long num_conflicting;
    unsigned long conflicting_fallbacks;
    unsigned long conflicting_fallbacks_same_inputs;
    unsigned long conflicting_fallbacks_no_true;
    unsigned long ast_info_cache_hits;
    unsigned long num_timeouts;
    double        avg_time_for_eval;
} fuzzy_stats_t;

typedef struct fuzzy_ctx_t {
    Z3_context    z3_ctx;
    char*         testcase_path;
    Z3_ast*       symbols;
    unsigned long n_symbols;
    fuzzy_stats_t stats;
    Z3_ast*       assignments;
    unsigned      size_assignments;
    uint64_t (*model_eval)(Z3_context, Z3_ast, uint64_t*, uint8_t*, size_t,
                           uint32_t*);
#ifdef FUZZY_SOURCE
    testcase_list_t testcases;
#else
    void* testcases_a;
    void* testcases_b;
    void* testcases_c;
#endif

    // opaque fields
    void* univocally_defined_inputs;
    void* ast_info_cache;
    void* processed_constraints;
    void* conflicting_asts;
    void* group_intervals;
    void* index_to_group_intervals;
    void* timer;
} fuzzy_ctx_t;

typedef struct memory_impact_stats_t {
    unsigned long univocally_defined_size;
    unsigned long ast_info_cache_size;
    unsigned long conflicting_ast_size;
    unsigned long group_intervals_size;
    unsigned long index_to_group_intervals_size;
    unsigned long n_assignments;
} memory_impact_stats_t;

fuzzy_ctx_t* z3fuzz_create(Z3_context ctx, char* seed_filename,
                           unsigned timeout);
void         z3fuzz_init(fuzzy_ctx_t* fctx, Z3_context ctx, char* seed_filename,
                         char* testcase_path,
                         uint64_t (*model_eval)(Z3_context, Z3_ast, uint64_t*, uint8_t*,
                                        size_t, uint32_t*),
                         unsigned timeout);
void         z3fuzz_free(fuzzy_ctx_t* ctx);
void         z3fuzz_print_expr(fuzzy_ctx_t* ctx, Z3_ast e);

unsigned long z3fuzz_evaluate_expression(fuzzy_ctx_t* ctx, Z3_ast value,
                                         unsigned char* values);
unsigned long z3fuzz_evaluate_expression_z3(fuzzy_ctx_t* ctx, Z3_ast query,
                                            Z3_ast* values);
int           z3fuzz_query_check_light(fuzzy_ctx_t* ctx, Z3_ast query,
                                       Z3_ast                branch_condition,
                                       unsigned char const** proof,
                                       unsigned long*        proof_size);
int z3fuzz_get_optimistic_sol(fuzzy_ctx_t* ctx, unsigned char const** proof,
                              unsigned long* proof_size);
unsigned long z3fuzz_maximize(fuzzy_ctx_t* ctx, Z3_ast pi, Z3_ast to_maximize,
                              unsigned char const** out_values,
                              unsigned long*        out_len);
unsigned long z3fuzz_minimize(fuzzy_ctx_t* ctx, Z3_ast pi, Z3_ast to_minimize,
                              unsigned char const** out_values,
                              unsigned long*        out_len);
void          z3fuzz_find_all_values(
             fuzzy_ctx_t* ctx, Z3_ast expr, Z3_ast pi,
             fuzzy_findall_res_t (*callback)(unsigned char const* out_bytes,
                                    unsigned long        out_bytes_len,
                                    unsigned long        val));
void z3fuzz_find_all_values_gd(
    fuzzy_ctx_t* ctx, Z3_ast expr, Z3_ast pi, int to_min,
    fuzzy_findall_res_t (*callback)(unsigned char const* out_bytes,
                                    unsigned long        out_bytes_len,
                                    unsigned long        val));
void z3fuzz_add_assignment(fuzzy_ctx_t* ctx, int idx, Z3_ast assignment_value);

void z3fuzz_notify_constraint(fuzzy_ctx_t* ctx, Z3_ast constraint);
void z3fuzz_dump_proof(fuzzy_ctx_t* ctx, const char* filename,
                       unsigned char const* proof, unsigned long proof_size);

void z3fuzz_get_mem_stats(fuzzy_ctx_t* ctx, memory_impact_stats_t* stats);
#endif