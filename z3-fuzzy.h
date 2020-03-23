#ifndef Z3_FUZZY_H
#define Z3_FUZZY_H

#include "testcase-list.h"
#include <z3.h>
#define Z3_VERSION 487

typedef struct fuzzy_stats_t {
    unsigned long num_evaluate;
    unsigned long num_sat;
    unsigned long L0;
    unsigned long L1;
    unsigned long L2;
    unsigned long L3;
    unsigned long L4_flip1;
    unsigned long L4_flip2;
    unsigned long L4_flip4;
    unsigned long L4_flip8;
    unsigned long L4_arith8_sum;
    unsigned long L4_arith8_sub;
    unsigned long L4_int8;
    unsigned long L4_flip16;
    unsigned long L4_arith16_sum_LE;
    unsigned long L4_arith16_sum_BE;
    unsigned long L4_arith16_sub_LE;
    unsigned long L4_arith16_sub_BE;
    unsigned long L4_int16;
    unsigned long L4_flip32;
    unsigned long L4_arith32_sum_LE;
    unsigned long L4_arith32_sum_BE;
    unsigned long L4_arith32_sub_LE;
    unsigned long L4_arith32_sub_BE;
    unsigned long L4_int32;
    unsigned long L5_havoc;
    unsigned long num_univocally_defined;
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
} fuzzy_ctx_t;

void z3fuzz_init(fuzzy_ctx_t* fctx, Z3_context ctx, char* seed_filename,
                 char* testcase_path,
                 uint64_t (*model_eval)(Z3_context, Z3_ast, uint64_t*, uint8_t*, size_t));
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