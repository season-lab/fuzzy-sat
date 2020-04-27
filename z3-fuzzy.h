#ifndef Z3_FUZZY_H
#define Z3_FUZZY_H

#include "testcase-list.h"
#include <z3.h>

typedef struct fuzzy_stats_t {
    unsigned long num_evaluate;
    unsigned long num_sat;
    unsigned long reuse;
    unsigned long input_to_state;
    unsigned long input_to_state_ext;
    unsigned long brute_force;
    unsigned long range_brute_force;
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
} fuzzy_stats_t;

typedef struct fuzzy_ctx_t {
    Z3_context    z3_ctx;
    char*         testcase_path;
    Z3_ast*       symbols;
    unsigned long n_symbols;
    fuzzy_stats_t stats;
    Z3_ast*       assignments;
    unsigned      size_assignments;
    uint64_t (*model_eval)(Z3_context, Z3_ast, uint64_t*, uint8_t*, size_t);
    testcase_list_t testcases;

    // opaque fields
    void* univocally_defined_inputs;
    void* assignment_inputs_cache;
    void* ast_info_cache;
    void* processed_constraints;
    void* conflicting_asts;
    void* group_intervals;
} fuzzy_ctx_t;

void z3fuzz_init(fuzzy_ctx_t* fctx, Z3_context ctx, char* seed_filename,
                 char* testcase_path,
                 uint64_t (*model_eval)(Z3_context, Z3_ast, uint64_t*, uint8_t*,
                                        size_t));
void z3fuzz_free(fuzzy_ctx_t* ctx);
void z3fuzz_print_expr(fuzzy_ctx_t* ctx, Z3_ast e);

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
void z3fuzz_add_assignment(fuzzy_ctx_t* ctx, int idx, Z3_ast assignment_value);

void z3fuzz_notify_constraint(fuzzy_ctx_t* ctx, Z3_ast constraint);
void z3fuzz_dump_proof(fuzzy_ctx_t* ctx, const char* filename,
                       unsigned char const* proof, unsigned long proof_size);

#endif