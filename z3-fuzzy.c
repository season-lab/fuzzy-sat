#include <assert.h>
#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>
#include "utility/md5.h"
#include "z3-fuzzy.h"

#ifndef likely
#define likely(x) __builtin_expect(!!(x), 1)
#endif
#ifndef unlikely
#define unlikely(x) __builtin_expect(!!(x), 0)
#endif

#define Z3FUZZ_LOG(x...) fprintf(stderr, "[z3fuzz] " x)
#define FLIP_BIT(_var, _idx) ((_var) ^ (1 << (_idx)));

// #define PRINT_SAT
// #define PRINT_NUM_EVALUATE
// #define LOG_QUERY_STATS
// #define DEBUG_CHECK_LIGHT

// #define CHECK_UNNECESSARY_EVALS
// #define SKIP_NOTIFY
// #define SKIP_DETERMINISTIC
#define SKIP_HAVOC

// generate parametric data structures
#include "z3-fuzzy-datastructures-gen.h"

uint64_t Z3_API Z3_custom_eval(Z3_context c, Z3_ast e, uint64_t* data,
                               uint8_t* data_sizes, size_t data_size);

typedef struct ast_data_t {
    // structure used to pass information during a single fuzzy sat execution
    unsigned linear_arithmetic_operations;
    unsigned nonlinear_arithmetic_operations;
    unsigned input_extract_ops;
    unsigned n_useless_eval;

    unsigned      is_input_to_state;
    index_group_t input_to_state_group;
    unsigned long input_to_state_const;
    unsigned long query_size;

    processed_set_t processed_set;
    index_groups_t  index_groups;
    indexes_t       indexes;
    values_t        values;
} ast_data_t;

static unsigned long* tmp_input = NULL;
static unsigned char* tmp_proof = NULL;
static ast_data_t     ast_data  = {0};

#ifdef LOG_QUERY_STATS
static char* query_log_filename = "/tmp/fuzzy-log-info.csv";
FILE*        query_log;
#endif

static char  interesting8[]  = {-128, -1, 0, 1, 16, 32, 64, 100, 127};
static short interesting16[] = {-32768, -129, 128,   255,  256, 512, 1000,
                                1024,   4096, 32767, -128, -1,  0,   1,
                                16,     32,   64,    100,  127};
static int   interesting32[] = {
    -2147483648, -100663046, -32769, 32768, 65535, 65536, 100663045,
    2147483647,  -32768,     -129,   128,   255,   256,   512,
    1000,        1024,       4096,   32767, -128,  -1,    0,
    1,           16,         32,     64,    100,   127};

#define RESEED_RNG 10000
static int             dev_urandom_fd = -1;
static unsigned        rand_cnt       = 1;
static inline unsigned UR(unsigned limit)
{
    if (unlikely(!rand_cnt--)) {
        unsigned seed[2];
        size_t   res = read(dev_urandom_fd, &seed, sizeof(seed));
        assert(res == sizeof(seed) && "read failed");
        srandom(seed[0]);
        rand_cnt = (RESEED_RNG / 2) + (seed[1] % RESEED_RNG);
    }
    return random() % limit;
}

static inline void print_index_and_value_queue(ast_data_t* data)
{
    index_group_t* group;
    fprintf(stderr, "----- QUEUE -----\n");
    unsigned int i, j;
    for (i = 0; i < data->values.size; ++i)
        fprintf(stderr, "value: 0x%lx\n", data->values.data[i]);

    i = 0;
    set_reset_iter__index_group_t(&data->index_groups, 1);
    while (set_iter_next__index_group_t(&data->index_groups, 1, &group)) {
        for (j = 0; j < group->n; ++j)
            fprintf(stderr, "group: %d. index: 0x%lx\n", i, group->indexes[j]);
        i++;
    }
    fprintf(stderr, "-----------------\n");
}

static inline void __symbol_init(fuzzy_ctx_t* ctx, unsigned long n_values)
{
    if (ctx->n_symbols >= n_values)
        return;

    unsigned int  i;
    Z3_sort       bsort         = Z3_mk_bv_sort(ctx->z3_ctx, 8);
    unsigned long old_n_symbols = ctx->n_symbols;

    if (ctx->symbols == NULL) {
        ctx->symbols   = (Z3_ast*)malloc(n_values * sizeof(Z3_ast));
        ctx->n_symbols = n_values;
    } else if (ctx->n_symbols < n_values) {
        ctx->symbols =
            (Z3_ast*)realloc(ctx->symbols, n_values * sizeof(Z3_ast));
        ctx->n_symbols = n_values;
    }

    for (i = old_n_symbols; i < ctx->n_symbols; ++i) {
        Z3_symbol s    = Z3_mk_int_symbol(ctx->z3_ctx, i);
        Z3_ast    s_bv = Z3_mk_const(ctx->z3_ctx, s, bsort);
        Z3_inc_ref(ctx->z3_ctx, s_bv);
        ctx->symbols[i] = s_bv;
    }
}

void z3fuzz_init(fuzzy_ctx_t* fctx, Z3_context ctx, char* seed_filename,
                 char* testcase_path,
                 uint64_t (*model_eval)(Z3_context, Z3_ast, uint64_t*, uint8_t*,
                                        size_t))
{
    Z3_set_ast_print_mode(ctx, Z3_PRINT_SMTLIB2_COMPLIANT);

    dev_urandom_fd = open("/dev/urandom", O_RDONLY);
    if (dev_urandom_fd < 0)
        assert(0 && "Unable to open /dev/urandom");

#ifdef LOG_QUERY_STATS
    query_log = fopen(query_log_filename, "w");
    fprintf(query_log,
            "query size;index size;index group size;is input to state;linear "
            "arith ops;non linear arith ops");
#endif

    fctx->model_eval    = model_eval != NULL ? model_eval : Z3_custom_eval;
    fctx->z3_ctx        = ctx;
    fctx->testcase_path = testcase_path;
    init_testcase_list(&fctx->testcases);
    load_testcase(&fctx->testcases, seed_filename, ctx);
    if (testcase_path != NULL)
        load_testcase_folder(&fctx->testcases, testcase_path, ctx);
    assert(fctx->testcases.size > 0 && "no testcase");

    fctx->assignments      = (Z3_ast*)calloc(10, sizeof(Z3_ast));
    fctx->size_assignments = 10;

    fctx->n_symbols = 0;
    fctx->symbols   = NULL;
    __symbol_init(fctx, fctx->testcases.data[0].values_len);

    testcase_t* current_testcase = &fctx->testcases.data[0];
    tmp_input = (unsigned long*)malloc(sizeof(unsigned long) *
                                       current_testcase->values_len);
    tmp_proof = (unsigned char*)malloc(sizeof(unsigned char) *
                                       current_testcase->testcase_len);

    fctx->univocally_defined_inputs = (void*)malloc(sizeof(set__ulong));
    set_init__ulong((set__ulong*)fctx->univocally_defined_inputs, &index_hash,
                    &index_equals);

    set_init__md5_digest_t(&ast_data.processed_set, &md5_64bit_hash,
                           &md5_digest_equals);
    set_init__index_group_t(&ast_data.index_groups, &index_group_hash,
                            &index_group_equals);
    set_init__ulong(&ast_data.indexes, &index_hash, &index_equals);
    da_init__ulong(&ast_data.values);
}

void z3fuzz_free(fuzzy_ctx_t* ctx)
{
    close(dev_urandom_fd);

#ifdef LOG_QUERY_STATS
    fclose(query_log);
#endif
    free_testcase_list(ctx->z3_ctx, &ctx->testcases);
    free(tmp_input);
    tmp_input = NULL;
    free(tmp_proof);
    tmp_proof = NULL;

    unsigned int i;
    for (i = 0; i < ctx->n_symbols; ++i)
        Z3_dec_ref(ctx->z3_ctx, ctx->symbols[i]);
    free(ctx->symbols);
    ctx->symbols   = NULL;
    ctx->n_symbols = 0;
    for (i = 0; i < ctx->size_assignments; ++i)
        if (ctx->assignments[i] != NULL)
            Z3_dec_ref(ctx->z3_ctx, ctx->assignments[i]);
    free(ctx->assignments);
    ctx->assignments      = NULL;
    ctx->size_assignments = 0;

    set_free__md5_digest_t(&ast_data.processed_set);
    set_free__index_group_t(&ast_data.index_groups);
    set_free__ulong(&ast_data.indexes);
    da_free__ulong(&ast_data.values, NULL);

    set_free__ulong((set__ulong*)ctx->univocally_defined_inputs);
    free(ctx->univocally_defined_inputs);

#ifdef PRINT_NUM_EVALUATE
    printf("num evaluate:\t%lu\n", ctx->stats.num_evaluate);
#endif
}

void z3fuzz_print_expr(fuzzy_ctx_t* ctx, Z3_ast e)
{
    Z3FUZZ_LOG("expr:\n%s\n", Z3_ast_to_string(ctx->z3_ctx, e));
}

static inline void __vals_char_to_long(unsigned char* in_vals,
                                       unsigned long* out_vals,
                                       unsigned long  n_vals)
{
    unsigned long i;
    for (i = 0; i < n_vals; ++i) {
        out_vals[i] = (unsigned long)(in_vals[i]);
    }
}

static inline void __vals_long_to_char(unsigned long* in_vals,
                                       unsigned char* out_vals,
                                       unsigned long  n_vals)
{
    unsigned long i;
    for (i = 0; i < n_vals; ++i)
        out_vals[i] = (unsigned char)in_vals[i];
}

static inline int __evaluate_branch_query(fuzzy_ctx_t* ctx, Z3_ast query,
                                          unsigned long* values,
                                          unsigned char* value_sizes,
                                          unsigned long  n_values)
{
    ctx->stats.num_evaluate++;

#ifdef CHECK_UNNECESSARY_EVALS
    md5_digest_t d;
    md5((unsigned char*)values, ctx->n_symbols * sizeof(unsigned long),
        d.digest);

    if (set_check__md5_digest_t(&ast_data.processed_set, d))
        return 0;
    set_add__md5_digest_t(&ast_data.processed_set, d);
#endif

    int res =
        (int)ctx->model_eval(ctx->z3_ctx, query, values, value_sizes, n_values);
    return res;
}

// *************************************************
// **** HEURISTICS - POPULATE ast_data_t struct ****
// *************************************************

static int __detect_input_group(fuzzy_ctx_t* ctx, Z3_ast node,
                                index_group_t* ig)
{
    int res;
    switch (Z3_get_ast_kind(ctx->z3_ctx, node)) {
        case Z3_APP_AST: {
            Z3_app       app        = Z3_to_app(ctx->z3_ctx, node);
            unsigned     num_fields = Z3_get_app_num_args(ctx->z3_ctx, app);
            Z3_func_decl decl       = Z3_get_app_decl(ctx->z3_ctx, app);
            Z3_decl_kind decl_kind  = Z3_get_decl_kind(ctx->z3_ctx, decl);
            unsigned     i;
            switch (decl_kind) {
                case Z3_OP_EXTRACT:
                case Z3_OP_BSHL:
                    ast_data.input_extract_ops++;
                case Z3_OP_CONCAT: {
                    // recursive call
                    res = 0;
                    for (i = 0; i < num_fields; ++i) {
                        res = __detect_input_group(
                            ctx, Z3_get_app_arg(ctx->z3_ctx, app, i), ig);
                        if (res == 0)
                            break;
                    }
                    break;
                }
                case Z3_OP_UNINTERPRETED: {
                    Z3_symbol s = Z3_get_decl_name(ctx->z3_ctx, decl);
                    unsigned  symbol_index =
                        (unsigned)Z3_get_symbol_int(ctx->z3_ctx, s);

                    if (symbol_index >= ctx->testcases.data[0].testcase_len)
                        // it is an assignment
                        return 0;

                    assert(ig->n < MAX_GROUP_SIZE &&
                           "__detect_input_group() unexpected "
                           "number of element in group");

                    int      already_in = 0;
                    unsigned i;
                    for (i = 0; i < ig->n; ++i) {
                        if (ig->indexes[i] == symbol_index)
                            already_in = 1;
                    }

                    if (!already_in) {
                        assert(ig->n < MAX_GROUP_SIZE &&
                               "__detect_input_group() unexpected "
                               "number of element in group");

                        ig->indexes[ig->n++] = symbol_index;
                    }
                    res = 1;
                    break;
                }
                default: {
                    res = 0;
                    break;
                }
            }
            break;
        }
        case Z3_NUMERAL_AST: {
            res = 1;
            break;
        }
        default: {
            res = 0;
            break;
        }
    }
    return res;
}

static void __detect_input_to_state_query(fuzzy_ctx_t* ctx, Z3_ast node,
                                          ast_data_t* data)
{
    Z3_ast_kind node_kind            = Z3_get_ast_kind(ctx->z3_ctx, node);
    unsigned    is_app               = node_kind == Z3_APP_AST;
    int         const_transformation = 0;

    Z3_app       node_app = is_app ? Z3_to_app(ctx->z3_ctx, node) : (Z3_app)0;
    Z3_func_decl node_decl =
        is_app ? Z3_get_app_decl(ctx->z3_ctx, node_app) : (Z3_func_decl)0;
    Z3_decl_kind node_decl_kind =
        is_app ? Z3_get_decl_kind(ctx->z3_ctx, node_decl) : (Z3_decl_kind)0;

    // condition 1 - root is a comparison (should always be the case)
    // also, save the comparison type
    if (!is_app) {
        data->is_input_to_state = 0;
        return;
    }

    unsigned is_neg;
    unsigned op_type;

    if (node_decl_kind == Z3_OP_EQ || node_decl_kind == Z3_OP_UGEQ ||
        node_decl_kind == Z3_OP_SGEQ || node_decl_kind == Z3_OP_ULEQ ||
        node_decl_kind == Z3_OP_SLEQ || node_decl_kind == Z3_OP_UGT ||
        node_decl_kind == Z3_OP_SGT || node_decl_kind == Z3_OP_ULT ||
        node_decl_kind == Z3_OP_SLT) {

        op_type = node_decl_kind;
        is_neg  = 0;
    } else if (node_decl_kind == Z3_OP_NOT) {
        Z3_ast      child        = Z3_get_app_arg(ctx->z3_ctx, node_app, 0);
        Z3_ast_kind child_kind   = Z3_get_ast_kind(ctx->z3_ctx, child);
        unsigned    child_is_app = child_kind == Z3_APP_AST;
        if (!child_is_app) {
            data->is_input_to_state = 0;
            return;
        }

        Z3_app       child_app  = Z3_to_app(ctx->z3_ctx, child);
        Z3_func_decl child_decl = Z3_get_app_decl(ctx->z3_ctx, child_app);
        Z3_decl_kind child_decl_kind =
            Z3_get_decl_kind(ctx->z3_ctx, child_decl);

        node_app       = child_app;
        node_decl      = child_decl;
        node_decl_kind = child_decl_kind;
        is_app         = child_is_app;

        if (child_decl_kind == Z3_OP_EQ || child_decl_kind == Z3_OP_UGEQ ||
            child_decl_kind == Z3_OP_SGEQ || child_decl_kind == Z3_OP_ULEQ ||
            child_decl_kind == Z3_OP_SLEQ || child_decl_kind == Z3_OP_UGT ||
            child_decl_kind == Z3_OP_SGT || child_decl_kind == Z3_OP_ULT ||
            child_decl_kind == Z3_OP_SLT) {

            op_type = child_decl_kind;
            is_neg  = 1;
        } else {
            data->is_input_to_state = 0;
            return;
        }
    } else {
        data->is_input_to_state = 0;
        return;
    }

    // condition 2 - one child is a constant
    int      condition_ok  = 0;
    unsigned const_operand = 0;
    unsigned num_fields    = Z3_get_app_num_args(ctx->z3_ctx, node_app);
    unsigned i;
    for (i = 0; i < num_fields; ++i) {
        Z3_ast child = Z3_get_app_arg(ctx->z3_ctx, node_app, i);
        if (Z3_get_ast_kind(ctx->z3_ctx, child) == Z3_NUMERAL_AST) {
            Z3_bool successGet = Z3_get_numeral_uint64(
                ctx->z3_ctx, child,
#if Z3_VERSION <= 451
                (long long unsigned int*)&data->input_to_state_const
#else
                (uint64_t*)&data->input_to_state_const
#endif
            );
            assert(successGet == Z3_TRUE && "failed to get constant");
            data->input_to_state_const += const_transformation;
            condition_ok  = 1;
            const_operand = i;
            break;
        }
    }

    if (!condition_ok) {
        data->is_input_to_state = 0;
        return;
    }

    // condition 3 - the other child is input-to-state
    condition_ok = __detect_input_group(
        ctx, Z3_get_app_arg(ctx->z3_ctx, node_app, const_operand == 1 ? 0 : 1),
        &data->input_to_state_group);

    if (!condition_ok) {
        data->is_input_to_state = 0;
        return;
    }

    if (is_neg && (op_type == Z3_OP_EQ || op_type == Z3_OP_UGEQ ||
                   op_type == Z3_OP_SGEQ)) {
        data->input_to_state_const += (const_operand == 0 ? 1 : -1);
    } else if (is_neg && (op_type == Z3_OP_ULEQ || op_type == Z3_OP_SLEQ)) {
        data->input_to_state_const += (const_operand == 0 ? -1 : 1);
    } else if (!is_neg && (op_type == Z3_OP_UGT || op_type == Z3_OP_SGT)) {
        data->input_to_state_const += (const_operand == 0 ? -1 : 1);
    } else if (!is_neg && (op_type == Z3_OP_ULT || op_type == Z3_OP_SLT)) {
        data->input_to_state_const += (const_operand == 1 ? -1 : 1);
    }

    data->is_input_to_state = 1;
    return;
}

static void __detect_involved_inputs(fuzzy_ctx_t* ctx, Z3_ast v,
                                     ast_data_t* data)
{
    // visit the AST and collect some data
    // 1. Find "groups" of inputs involved in the AST and store them in
    // 'index_queue'
    // 2. Populate global 'indexes' with encountered indexes
    switch (Z3_get_ast_kind(ctx->z3_ctx, v)) {
        case Z3_NUMERAL_AST: {
            data->query_size++;
            break;
        }
        case Z3_APP_AST: {
            data->query_size++;
            unsigned     i;
            Z3_app       app        = Z3_to_app(ctx->z3_ctx, v);
            unsigned     num_fields = Z3_get_app_num_args(ctx->z3_ctx, app);
            Z3_func_decl decl       = Z3_get_app_decl(ctx->z3_ctx, app);
            Z3_decl_kind decl_kind  = Z3_get_decl_kind(ctx->z3_ctx, decl);

            switch (decl_kind) {
                case Z3_OP_BSHL:
                case Z3_OP_EXTRACT:
                    data->input_extract_ops++;
                case Z3_OP_CONCAT: {
                    index_group_t group = {0};
                    if (__detect_input_group(ctx, v, &group)) {
                        // concat chain. commit
                        set_add__index_group_t(
                            &data->index_groups,
                            group); // i'm not checking whether the elements
                                    // of the input group are univocally
                                    // defined. This because it can be that
                                    // only a subset is univocally defined...
                                    // In this case I should add the group. I
                                    // need to add this check

                        unsigned i;
                        for (i = 0; i < group.n; ++i) {
                            if (!set_check__ulong(
                                    (set__ulong*)ctx->univocally_defined_inputs,
                                    group.indexes[i]))
                                set_add__ulong(&data->indexes,
                                               group.indexes[i]);
                        }
                        return;
                    }
                    break;
                }
                case Z3_OP_UNINTERPRETED: {
                    index_group_t group = {0};
                    Z3_symbol     s     = Z3_get_decl_name(ctx->z3_ctx, decl);
                    int symbol_index    = Z3_get_symbol_int(ctx->z3_ctx, s);

                    if (symbol_index >= ctx->testcases.data[0].testcase_len) {
                        // the symbol is indeed an assignment. Resolve the
                        // assignment

                        __detect_involved_inputs(
                            ctx, ctx->assignments[symbol_index], data);
                        break;
                    }

                    group.indexes[group.n++] = symbol_index;

                    if (!set_check__ulong(
                            (set__ulong*)ctx->univocally_defined_inputs,
                            symbol_index)) {
                        set_add__index_group_t(&data->index_groups, group);
                        set_add__ulong(&data->indexes, symbol_index);
                    }
                    return;
                }
                case Z3_OP_BLSHR:
                case Z3_OP_BASHR:
                    data->input_extract_ops++;
                case Z3_OP_BADD:
                case Z3_OP_BSUB:
                case Z3_OP_BMUL: {
                    data->linear_arithmetic_operations++;
                    break;
                }
                case Z3_OP_BAND:
                case Z3_OP_BUREM:
                case Z3_OP_BUREM_I:
                case Z3_OP_BSREM:
                case Z3_OP_BSREM_I:
                case Z3_OP_BSMOD:
                    data->input_extract_ops++;
                case Z3_OP_OR:
                case Z3_OP_BXOR: {
                    data->nonlinear_arithmetic_operations++;
                    break;
                }
                default: {
                    break;
                }
            }
            if (num_fields > 0) {
                for (i = 0; i < num_fields; i++) {
                    __detect_involved_inputs(
                        ctx, Z3_get_app_arg(ctx->z3_ctx, app, i), data);
                }
            }
            break;
        }
        case Z3_QUANTIFIER_AST: {
            assert(0 && "__main_ast_visit() found quantifier\n");
        }
        default:
            assert(0 && "__main_ast_visit() unknown ast kind\n");
    }
}

static void __detect_early_constants(fuzzy_ctx_t* ctx, Z3_ast v,
                                     ast_data_t* data)
{
    // look for constants in early SUB/AND and in early EQ/GE/GT/LE/LT/SLE/SLT
    unsigned long tmp_const;
    switch (Z3_get_ast_kind(ctx->z3_ctx, v)) {
        case Z3_APP_AST: {
            Z3_bool      successGet;
            Z3_ast       child1, child2;
            Z3_app       app       = Z3_to_app(ctx->z3_ctx, v);
            Z3_func_decl decl      = Z3_get_app_decl(ctx->z3_ctx, app);
            Z3_decl_kind decl_kind = Z3_get_decl_kind(ctx->z3_ctx, decl);

            switch (decl_kind) {
                case Z3_OP_EXTRACT:
                case Z3_OP_NOT: {
                    // unary forward
                    child1 = Z3_get_app_arg(ctx->z3_ctx, app, 0);
                    __detect_early_constants(ctx, child1, data);
                    break;
                }
                case Z3_OP_CONCAT: {
                    child1 = Z3_get_app_arg(ctx->z3_ctx, app, 0);
                    child2 = Z3_get_app_arg(ctx->z3_ctx, app, 1);
                    __detect_early_constants(ctx, child1, data);
                    __detect_early_constants(ctx, child2, data);
                    break;
                }
                case Z3_OP_EQ:
                case Z3_OP_UGEQ:
                case Z3_OP_SGEQ:
                case Z3_OP_UGT:
                case Z3_OP_SGT:
                case Z3_OP_ULEQ:
                case Z3_OP_ULT:
                case Z3_OP_SLT:
                case Z3_OP_SLEQ: {
                    child1 = Z3_get_app_arg(ctx->z3_ctx, app, 0);
                    child2 = Z3_get_app_arg(ctx->z3_ctx, app, 1);

                    if (Z3_get_ast_kind(ctx->z3_ctx, child1) ==
                        Z3_NUMERAL_AST) {
                        successGet = Z3_get_numeral_uint64(
                            ctx->z3_ctx, child1,
#if Z3_VERSION <= 451
                            (long long unsigned int*)&tmp_const
#else
                            (uint64_t*)&tmp_const
#endif
                        );
                        assert(successGet == Z3_TRUE &&
                               "failed to get constant");
                        da_add_item__ulong(&data->values, tmp_const);
                        da_add_item__ulong(&data->values, tmp_const + 1);
                        da_add_item__ulong(&data->values, tmp_const - 1);
                    } else if (Z3_get_ast_kind(ctx->z3_ctx, child2) ==
                               Z3_NUMERAL_AST) {
                        successGet = Z3_get_numeral_uint64(
                            ctx->z3_ctx, child2,
#if Z3_VERSION <= 451
                            (long long unsigned int*)&tmp_const
#else
                            (uint64_t*)&tmp_const
#endif
                        );
                        assert(successGet == Z3_TRUE &&
                               "failed to get constant");
                        da_add_item__ulong(&data->values, tmp_const);
                        da_add_item__ulong(&data->values, tmp_const + 1);
                        da_add_item__ulong(&data->values, tmp_const - 1);
                    }

                    // binary forward
                    __detect_early_constants(ctx, child1, data);
                    __detect_early_constants(ctx, child2, data);
                    break;
                }
                case Z3_OP_BSUB:
                case Z3_OP_BAND: {
                    // look for constant
                    child1 = Z3_get_app_arg(ctx->z3_ctx, app, 0);
                    child2 = Z3_get_app_arg(ctx->z3_ctx, app, 1);

                    if (Z3_get_ast_kind(ctx->z3_ctx, child1) ==
                        Z3_NUMERAL_AST) {
                        successGet = Z3_get_numeral_uint64(
                            ctx->z3_ctx, child1,
#if Z3_VERSION <= 451
                            (long long unsigned int*)&tmp_const
#else
                            (uint64_t*)&tmp_const
#endif
                        );
                        assert(successGet == Z3_TRUE &&
                               "failed to get constant");
                        da_add_item__ulong(&data->values, tmp_const);
                        da_add_item__ulong(&data->values, tmp_const + 1);
                        da_add_item__ulong(&data->values, tmp_const - 1);
                    } else if (Z3_get_ast_kind(ctx->z3_ctx, child2) ==
                               Z3_NUMERAL_AST) {
                        successGet = Z3_get_numeral_uint64(
                            ctx->z3_ctx, child2,
#if Z3_VERSION <= 451
                            (long long unsigned int*)&tmp_const
#else
                            (uint64_t*)&tmp_const
#endif
                        );
                        assert(successGet == Z3_TRUE &&
                               "failed to get constant");
                        da_add_item__ulong(&data->values, tmp_const);
                        da_add_item__ulong(&data->values, tmp_const + 1);
                        da_add_item__ulong(&data->values, tmp_const - 1);
                    }
                    break;
                }
                default: {
                    break;
                }
            }
            break;
        }
        default: {
            break;
        }
    }
    return;
}

static inline int __check_univocally_defined(fuzzy_ctx_t* ctx, Z3_ast expr,
                                             ast_data_t* data)
{
    Z3_ast_kind kind = Z3_get_ast_kind(ctx->z3_ctx, expr);
    if (kind != Z3_APP_AST)
        return 0;

    Z3_app       app       = Z3_to_app(ctx->z3_ctx, expr);
    Z3_func_decl decl      = Z3_get_app_decl(ctx->z3_ctx, app);
    Z3_decl_kind decl_kind = Z3_get_decl_kind(ctx->z3_ctx, decl);

    if (decl_kind != Z3_OP_EQ)
        return 0;

    set_remove_all__index_group_t(&ast_data.index_groups);
    ast_data.input_extract_ops = 0;
    __detect_involved_inputs(ctx, expr, &ast_data);
    if (ast_data.input_extract_ops > 0)
        return 0; // it is not safe to add to univocally defined

    if (data->index_groups.size != 1)
        return 0;

    // we have (= something f(INPUT)) in the branch condition
    // from now on, INPUT is univocally defined (from seed!)
    // never add INPUT to indexes/index_groups again
    index_group_t* ig = NULL;
    set_reset_iter__index_group_t(&data->index_groups, 0);
    set_iter_next__index_group_t(&data->index_groups, 0, &ig);

    unsigned i;
    for (i = 0; i < ig->n; ++i) {
        set_add__ulong((set__ulong*)ctx->univocally_defined_inputs,
                       ig->indexes[i]);
    }
    return 1;
}

// *************************************************
// **************** HEURISTICS - END ***************
// *************************************************

static inline void __reset_ast_data()
{
    set_remove_all__md5_digest_t(&ast_data.processed_set);
    set_remove_all__index_group_t(&ast_data.index_groups);
    set_remove_all__ulong(&ast_data.indexes);
    da_remove_all__ulong(&ast_data.values);

    ast_data.linear_arithmetic_operations    = 0;
    ast_data.nonlinear_arithmetic_operations = 0;
    ast_data.input_to_state_group.n          = 0;
    ast_data.query_size                      = 0;
    ast_data.input_extract_ops               = 0;
    ast_data.n_useless_eval                  = 0;
}

static inline void __init_global_data(fuzzy_ctx_t* ctx, Z3_ast query,
                                      Z3_ast branch_condition)
{

    __reset_ast_data();

    __detect_input_to_state_query(ctx, branch_condition, &ast_data);
    __detect_involved_inputs(ctx, branch_condition, &ast_data);
    __detect_early_constants(ctx, branch_condition, &ast_data);

    testcase_t* current_testcase = &ctx->testcases.data[0];
    memcpy(tmp_input, current_testcase->values,
           current_testcase->values_len * sizeof(unsigned long));
}

static inline unsigned char __extract_from_long(long value, unsigned int i)
{
    return (value >> i * 8) & 0xff;
}

static int __query_check_light(fuzzy_ctx_t* ctx, Z3_ast query,
                               Z3_ast                branch_condition,
                               unsigned char const** proof,
                               unsigned long*        proof_size)
{
    // 1 -> succeded
#ifdef DEBUG_CHECK_LIGHT
    // Z3FUZZ_LOG("query: \n%s\n", Z3_ast_to_string(ctx->z3_ctx, query));
    Z3FUZZ_LOG("branch condition: \n%s\n\n",
               Z3_ast_to_string(ctx->z3_ctx, branch_condition));
#endif

    unsigned int   i, k;
    unsigned int   index;
    unsigned char  b;
    unsigned char* testcase_copy;
    testcase_t*    current_testcase = &ctx->testcases.data[0];
    testcase_t*    testcase;
    index_group_t* group;
    unsigned long* uniq_index;

    // havoc defs
    int             havoc_res;
    index_group_t*  random_group;
    unsigned long   random_index;
    unsigned long   index_0;
    unsigned long   index_1;
    unsigned long   index_2;
    unsigned long   index_3;
    unsigned char   val_0;
    unsigned char   val_1;
    unsigned char   val_2;
    unsigned char   val_3;
    unsigned        tmp;
    unsigned        random_tmp;
    unsigned        mutation_pool;
    unsigned        score;
    unsigned long*  indexes;
    unsigned long   indexes_size;
    index_group_t** ig_16;
    unsigned long   ig_16_size;
    index_group_t** ig_32;
    unsigned long   ig_32_size;
    index_group_t** ig_64;
    unsigned long   ig_64_size;

    // L0 -- REUSE
    if (ctx->testcases.size < 2)
        // we have only the seed. skip L0
        goto L1;

#ifdef DEBUG_CHECK_LIGHT
    Z3FUZZ_LOG("Trying L0\n");
#endif

    for (i = 1; i < ctx->testcases.size; ++i) {
        testcase = &ctx->testcases.data[i];

        if (__evaluate_branch_query(ctx, query, testcase->values,
                                    testcase->value_sizes,
                                    testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light L0] Query is SAT\n");
#endif
            __vals_long_to_char(testcase->values, tmp_proof,
                                testcase->testcase_len);
            ctx->stats.L0++;
            *proof      = tmp_proof;
            *proof_size = testcase->testcase_len;
            return 1;
        }
    }

    // L1 -- INPUT TO STATE
L1:
    // common code, this must be executed for the subsequent levels to work
    __init_global_data(ctx, query, branch_condition);
#ifdef LOG_QUERY_STATS
    fprintf(query_log, "\n%lu;%lu;%lu;%s;%u;%u", ast_data.query_size,
            ast_data.indexes.size, ast_data.index_groups.size,
            ast_data.is_input_to_state ? "true" : "false",
            ast_data.linear_arithmetic_operations,
            ast_data.nonlinear_arithmetic_operations);
#endif
    if (ast_data.indexes.size == 0) { // constant branch condition!
        return __evaluate_branch_query(ctx, query, tmp_input,
                                       current_testcase->value_sizes,
                                       current_testcase->values_len);
    }
    // ********************************************************************

#ifdef DEBUG_CHECK_LIGHT
    print_index_and_value_queue(&ast_data);
#endif

    if (ast_data.is_input_to_state == 0)
        // input to state not detected
        goto L2;

#ifdef DEBUG_CHECK_LIGHT
    Z3FUZZ_LOG("Trying L1\n");
#endif

    group = &ast_data.input_to_state_group;
    for (k = 0; k < group->n; ++k) {
        index = group->indexes[group->n - k - 1];
        b     = __extract_from_long(ast_data.input_to_state_const, k);

        if (current_testcase->values[index] == (unsigned long)b)
            continue;

#ifdef DEBUG_CHECK_LIGHT
        Z3FUZZ_LOG("L1 - inj byte: 0x%x @ %d\n", b, index);
#endif
        tmp_input[index] = b;
    }
    if (__evaluate_branch_query(ctx, query, tmp_input,
                                current_testcase->value_sizes,
                                current_testcase->values_len)) {
#ifdef PRINT_SAT
        Z3FUZZ_LOG("[check light L1] Query is SAT\n");
#endif
        ctx->stats.L1++;
        ctx->stats.num_sat++;
        __vals_long_to_char(tmp_input, tmp_proof,
                            current_testcase->testcase_len);
        *proof      = tmp_proof;
        *proof_size = current_testcase->testcase_len;
        return 1;
    }
    // restore tmp_input
    for (k = 0; k < group->n; ++k) {
        index            = group->indexes[group->n - k - 1];
        tmp_input[index] = (unsigned long)current_testcase->values[index];
    }

    // L2 -- INPUT TO STATE EXTENDED
L2:
    if (ast_data.values.size == 0) {
        // no early constant
        goto L3;
    }

    for (i = 0; i < ast_data.values.size; ++i) {
        set_reset_iter__index_group_t(&ast_data.index_groups, 0);
        while (
            set_iter_next__index_group_t(&ast_data.index_groups, 0, &group)) {
            for (k = 0; k < group->n; ++k) {
                unsigned int  index = group->indexes[group->n - k - 1];
                unsigned char b =
                    __extract_from_long(ast_data.values.data[i], k);

#ifdef DEBUG_CHECK_LIGHT
                Z3FUZZ_LOG("L2 - inj byte: 0x%x @ %d\n", b, index);
#endif
                if (current_testcase->values[index] == (unsigned long)b)
                    continue;

                tmp_input[index] = b;
            }
            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->values_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L2] Query is SAT\n");
#endif
                ctx->stats.L2++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->values_len;
                return 1;
            }
            // restore tmp_input
            for (k = 0; k < group->n; ++k) {
                index            = group->indexes[group->n - k - 1];
                tmp_input[index] = current_testcase->values[index];
            }
        }
    }

    // L3 -- PURE BRUTE FORCE - ONLY ONE BYTE IS INVOLVED
L3:

    if (ast_data.indexes.size != 1) {
        // too much entropy
        goto L4;
    }
#ifdef DEBUG_CHECK_LIGHT
    Z3FUZZ_LOG("Trying L3\n");
#endif

    uniq_index = NULL;
    set_reset_iter__ulong(&ast_data.indexes, 0);
    set_iter_next__ulong(&ast_data.indexes, 0, &uniq_index);

    for (i = 0; i < 256; ++i) {
        tmp_input[*uniq_index] = i;
        if (__evaluate_branch_query(ctx, query, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
            ctx->stats.L3++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
    }
    // if we are here, the query is UNSAT
    return 0;

    // L4 -- DETERMINISTIC AFL TRANSFORMATIONS
L4:

#ifdef DEBUG_CHECK_LIGHT
    Z3FUZZ_LOG("Trying L4\n");
#endif

#ifdef SKIP_DETERMINISTIC
    goto L5;
#endif

    set_reset_iter__ulong(&ast_data.indexes, 1);

    ulong* p;

    unsigned long input_index_0, input_index_1, input_index_2, input_index_3;
    unsigned char input_byte_0, input_byte_1, input_byte_2, input_byte_3;

    unsigned short input_word_LE, input_word_BE;
    unsigned int   input_dword_LE, input_dword_BE;

    while (set_iter_next__ulong(&ast_data.indexes, 1, &p)) {
        input_index_0 = *p;
        // ****************
        // ***** byte *****
        // ****************
        input_byte_0 = (unsigned char)current_testcase->values[input_index_0];
        unsigned char tmp_byte;

        // single walking bit
        for (i = 0; i < 8; ++i) {
            tmp_byte                 = FLIP_BIT(input_byte_0, i);
            tmp_input[input_index_0] = (unsigned long)tmp_byte;
            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->values_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - flip1] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_flip1++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
        }

        // two walking bits
        for (i = 0; i < 7; ++i) {
            tmp_byte                 = FLIP_BIT(input_byte_0, i);
            tmp_byte                 = FLIP_BIT(tmp_byte, i + 1);
            tmp_input[input_index_0] = (unsigned long)tmp_byte;
            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->testcase_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - flip2] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_flip2++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
        }

        // four walking bits
        for (i = 0; i < 5; ++i) {
            tmp_byte                 = FLIP_BIT(input_byte_0, i);
            tmp_byte                 = FLIP_BIT(tmp_byte, i + 1);
            tmp_byte                 = FLIP_BIT(tmp_byte, i + 2);
            tmp_byte                 = FLIP_BIT(tmp_byte, i + 3);
            tmp_input[input_index_0] = (unsigned long)tmp_byte;
            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->testcase_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - flip4] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_flip4++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
        }

        // byte flip
        tmp_input[input_index_0] = (unsigned long)input_byte_0 ^ 0xffUL;
        if (__evaluate_branch_query(ctx, query, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light L4 - flip8] "
                       "Query is SAT\n");
#endif
            ctx->stats.L4_flip8++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }

        // 8-bit arithmetics
        for (i = 1; i < 35; ++i) {
            tmp_input[input_index_0] = (unsigned char)(input_byte_0 + i);
            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->values_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - arith8-sum] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_arith8_sum++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
            tmp_input[input_index_0] = (unsigned char)(input_byte_0 - i);
            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->values_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - arith8-sub] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_arith8_sub++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
        }

        // interesting 8
        for (i = 0; i < sizeof(interesting8); ++i) {
            tmp_input[input_index_0] = (unsigned char)(interesting8[i]);
            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->values_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - int8] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_int8++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
        }

        tmp_input[input_index_0] =
            (unsigned long)current_testcase->values[input_index_0];

        if (!set_check__ulong(&ast_data.indexes, input_index_0 + 1))
            continue; // only one byte. Skip

        // ****************
        // ***** word *****
        // ****************
        input_index_1 = input_index_0 + 1;
        input_byte_1  = (unsigned char)current_testcase->values[input_index_1];
        input_word_LE = (input_byte_1 << 8) | input_byte_0;
        input_word_BE = (input_byte_0 << 8) | input_byte_1;

        // flip short
        tmp_input[input_index_0] = (unsigned long)input_byte_0 ^ 0xffUL;
        tmp_input[input_index_1] = (unsigned long)input_byte_1 ^ 0xffUL;
        if (__evaluate_branch_query(ctx, query, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light L4 - flip16] "
                       "Query is SAT\n");
#endif
            ctx->stats.L4_flip16++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }

        // 16-bit arithmetics
        for (i = 1; i < 35; ++i) {
            tmp_input[input_index_0] =
                (unsigned long)(input_word_LE + i) & 0xffUL;
            tmp_input[input_index_1] =
                (unsigned long)((input_word_LE + i) >> 8) & 0xffUL;

            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->values_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - arith16-sum-LE] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_arith16_sum_LE++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
            tmp_input[input_index_0] =
                (unsigned long)(input_word_LE - i) & 0xffUL;
            tmp_input[input_index_1] =
                (unsigned long)((input_word_LE - i) >> 8) & 0xffUL;

            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->values_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - arith16-sub-LE] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_arith16_sub_LE++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
            tmp_input[input_index_0] =
                (unsigned long)(input_word_BE + i) & 0xffUL;
            tmp_input[input_index_1] =
                (unsigned long)((input_word_BE + i) >> 8) & 0xffUL;

            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->values_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - arith16-sum-BE] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_arith16_sum_BE++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
            tmp_input[input_index_0] =
                (unsigned long)(input_word_BE - i) & 0xffUL;
            tmp_input[input_index_1] =
                (unsigned long)((input_word_BE - i) >> 8) & 0xffUL;

            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->values_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - arith16-sub-BE] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_arith32_sub_BE++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
        }

        // interesting 16
        for (i = 0; i < sizeof(interesting16) / sizeof(short); ++i) {
            tmp_input[input_index_0] =
                (unsigned long)(interesting16[i]) & 0xffUL;
            tmp_input[input_index_1] =
                (unsigned long)(interesting16[i] >> 8) & 0xffUL;

            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->testcase_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - int16] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_int16++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
        }
        tmp_input[input_index_0] = current_testcase->values[input_index_0];
        tmp_input[input_index_1] = current_testcase->values[input_index_1];

        if (!set_check__ulong(&ast_data.indexes, input_index_0 + 2) ||
            !set_check__ulong(&ast_data.indexes, input_index_0 + 3))
            continue; // not enough bytes. Skip

        // ***************
        // **** dword ****
        // ***************
        input_index_2 = input_index_0 + 2;
        input_index_3 = input_index_0 + 3;
        input_byte_2  = (unsigned char)current_testcase->values[input_index_2];
        input_byte_3  = (unsigned char)current_testcase->values[input_index_3];
        input_dword_LE =
            (((input_byte_3 << 8) | input_byte_2) << 16) | input_word_LE;
        input_dword_BE =
            (input_word_BE << 16) | (input_byte_2 << 8) | input_byte_3;

        // flip int
        tmp_input[input_index_0] = (unsigned long)input_byte_0 ^ 0xffUL;
        tmp_input[input_index_1] = (unsigned long)input_byte_1 ^ 0xffUL;
        tmp_input[input_index_2] = (unsigned long)input_byte_2 ^ 0xffUL;
        tmp_input[input_index_3] = (unsigned long)input_byte_3 ^ 0xffUL;

        if (__evaluate_branch_query(ctx, query, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light L4 - flip32] "
                       "Query is SAT\n");
#endif
            ctx->stats.L4_flip32++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }

        // 32-bit arithmetics
        for (i = 1; i < 35; ++i) {
            tmp_input[input_index_0] =
                (unsigned long)(input_dword_LE + i) & 0xffUL;
            tmp_input[input_index_1] =
                (unsigned long)((input_dword_LE + i) >> 8) & 0xffUL;
            tmp_input[input_index_2] =
                (unsigned long)((input_dword_LE + i) >> 16) & 0xffUL;
            tmp_input[input_index_3] =
                (unsigned long)((input_dword_LE + i) >> 24) & 0xffUL;

            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->values_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - arith32-sum-LE] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_arith32_sum_LE++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
            tmp_input[input_index_0] =
                (unsigned long)(input_dword_LE - i) & 0xffUL;
            tmp_input[input_index_1] =
                (unsigned long)((input_dword_LE - i) >> 8) & 0xffUL;
            tmp_input[input_index_2] =
                (unsigned long)((input_dword_LE - i) >> 16) & 0xffUL;
            tmp_input[input_index_3] =
                (unsigned long)((input_dword_LE - i) >> 24) & 0xffUL;

            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->values_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - arith32-sub-LE] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_arith32_sub_LE++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
            tmp_input[input_index_0] =
                (unsigned long)(input_dword_BE + i) & 0xffUL;
            tmp_input[input_index_1] =
                (unsigned long)((input_dword_BE + i) >> 8) & 0xffUL;
            tmp_input[input_index_2] =
                (unsigned long)((input_dword_BE + i) >> 16) & 0xffUL;
            tmp_input[input_index_3] =
                (unsigned long)((input_dword_BE + i) >> 24) & 0xffUL;

            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->testcase_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - arith32-sum-BE] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_arith16_sum_BE++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
            tmp_input[input_index_0] =
                (unsigned long)(input_dword_BE - i) & 0xffU;
            tmp_input[input_index_1] =
                (unsigned long)((input_dword_BE - i) >> 8) & 0xffU;
            tmp_input[input_index_2] =
                (unsigned long)((input_dword_BE - i) >> 16) & 0xffU;
            tmp_input[input_index_3] =
                (unsigned long)((input_dword_BE - i) >> 24) & 0xffU;

            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->testcase_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - arith32-sub-BE] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_arith32_sub_BE++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
        }

        // interesting 32
        for (i = 0; i < sizeof(interesting32) / sizeof(int); ++i) {
            tmp_input[input_index_0] =
                (unsigned long)(interesting32[i]) & 0xffU;
            tmp_input[input_index_1] =
                (unsigned long)(interesting32[i] >> 8) & 0xffU;
            tmp_input[input_index_2] =
                (unsigned long)(interesting32[i] >> 16) & 0xffU;
            tmp_input[input_index_3] =
                (unsigned long)(interesting32[i] >> 24) & 0xffU;

            if (__evaluate_branch_query(ctx, query, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->testcase_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG("[check light L4 - int32] "
                           "Query is SAT\n");
#endif
                ctx->stats.L4_int32++;
                ctx->stats.num_sat++;
                __vals_long_to_char(tmp_input, tmp_proof,
                                    current_testcase->testcase_len);
                *proof      = tmp_proof;
                *proof_size = current_testcase->testcase_len;
                return 1;
            }
        }

        tmp_input[input_index_0] = current_testcase->values[input_index_0];
        tmp_input[input_index_1] = current_testcase->values[input_index_1];
        tmp_input[input_index_2] = current_testcase->values[input_index_2];
        tmp_input[input_index_3] = current_testcase->values[input_index_3];
    }

    // L5 -- HAVOC
// L5:
#ifdef SKIP_HAVOC
    goto L6;
#endif

    // initialize list input
    indexes =
        (unsigned long*)malloc(ast_data.indexes.size * sizeof(unsigned long));
    indexes_size = ast_data.indexes.size;
    // initialize groups input
    ig_16      = (index_group_t**)malloc(ast_data.index_groups.size *
                                    sizeof(index_group_t*));
    ig_16_size = 0;
    ig_32      = (index_group_t**)malloc(ast_data.index_groups.size *
                                    sizeof(index_group_t*));
    ig_32_size = 0;
    ig_64      = (index_group_t**)malloc(ast_data.index_groups.size *
                                    sizeof(index_group_t*));
    ig_64_size = 0;

    i = 0;
    set_reset_iter__ulong(&ast_data.indexes, 1);
    while (set_iter_next__ulong(&ast_data.indexes, 1, &p)) {
        indexes[i++] = *p;
    }
    set_reset_iter__index_group_t(&ast_data.index_groups, 1);
    while (set_iter_next__index_group_t(&ast_data.index_groups, 1, &group)) {
        switch (group->n) {
            case 1:
                break;
            case 2:
                ig_16[ig_16_size++] = group;
                break;
            case 4:
                ig_32[ig_32_size++] = group;
                break;
            case 8:
                ig_64[ig_64_size++] = group;
                break;
            default:
                assert(0 && "unexpected group size");
        }
    }

    havoc_res     = 0;
    mutation_pool = 5 + (ig_64_size + ig_32_size + ig_16_size > 0 ? 3 : 0) +
                    (ig_64_size + ig_32_size > 0 ? 3 : 0);
    score = 1000; // TODO
    for (i = 0; i < score; ++i) {
        switch (UR(mutation_pool)) {
            case 0: {
                // flip bit
                random_index = indexes[UR(indexes_size)];
                tmp_input[random_index] =
                    (unsigned long)FLIP_BIT(tmp_input[random_index], UR(8));
                break;
            }
            case 1: {
                // set interesting byte
                random_index            = indexes[UR(indexes_size)];
                tmp_input[random_index] = (unsigned long)
                    interesting8[UR(sizeof(interesting8) / sizeof(char))];
                break;
            }
            case 2: {
                // random subtract byte
                random_index = indexes[UR(indexes_size)];
                tmp_input[random_index] -= (unsigned char)(UR(35) + 1);
                break;
            }
            case 3: {
                // random add byte
                random_index = indexes[UR(indexes_size)];
                tmp_input[random_index] += (unsigned char)(UR(35) + 1);
                break;
            }
            case 4: {
                // random, byte set
                random_index = indexes[UR(indexes_size)];
                tmp_input[random_index] ^= (unsigned char)(UR(255) + 1);
                break;
            }
            case 5: {
                // set interesting word
                unsigned pool = UR(ig_16_size + ig_32_size + ig_64_size);
                if (pool < ig_16_size) {
                    // word group
                    random_group = ig_16[pool];
                    index_0      = random_group->indexes[0];
                    index_1      = random_group->indexes[1];
                } else if (pool < ig_32_size + ig_16_size) {
                    // dword group
                    random_group = ig_32[pool - ig_16_size];
                    random_tmp   = UR(3);
                    index_0      = random_group->indexes[random_tmp];
                    index_1      = random_group->indexes[random_tmp + 1];
                } else {
                    // qword group
                    random_group = ig_64[pool - ig_32_size - ig_16_size];
                    random_tmp   = UR(7);
                    index_0      = random_group->indexes[random_tmp];
                    index_1      = random_group->indexes[random_tmp + 1];
                }

                short interesting_16 =
                    interesting16[UR(sizeof(interesting16) / sizeof(short))];
                val_0 = interesting_16 & 0xff;
                val_1 = (interesting_16 >> 8) & 0xff;
                if (UR(2)) {
                    tmp     = index_0;
                    index_0 = index_1;
                    index_1 = tmp;
                }
                tmp_input[index_0] = val_0;
                tmp_input[index_1] = val_1;
                break;
            }
            case 6: {
                // random subtract word
                unsigned pool = UR(ig_16_size + ig_32_size + ig_64_size);
                if (pool < ig_16_size) {
                    // word group
                    random_group = ig_16[pool];
                    index_0      = random_group->indexes[0];
                    index_1      = random_group->indexes[1];
                } else if (pool < ig_32_size + ig_16_size) {
                    // dword group
                    random_group = ig_32[pool - ig_16_size];
                    random_tmp   = UR(3);
                    index_0      = random_group->indexes[random_tmp];
                    index_1      = random_group->indexes[random_tmp + 1];
                } else {
                    // qword group
                    random_group = ig_64[pool - ig_32_size - ig_16_size];
                    random_tmp   = UR(7);
                    index_0      = random_group->indexes[random_tmp];
                    index_1      = random_group->indexes[random_tmp + 1];
                }

                if (UR(2)) {
                    tmp     = index_0;
                    index_0 = index_1;
                    index_1 = tmp;
                }
                short val = (tmp_input[index_1] << 8) | tmp_input[index_0];
                val -= UR(35) + 1;
                tmp_input[index_0] = val & 0xff;
                tmp_input[index_1] = (val >> 8) & 0xff;
                break;
            }
            case 7: {
                // random add word
                unsigned pool = UR(ig_16_size + ig_32_size + ig_64_size);
                if (pool < ig_16_size) {
                    // word group
                    random_group = ig_16[pool];
                    index_0      = random_group->indexes[0];
                    index_1      = random_group->indexes[1];
                } else if (pool < ig_32_size + ig_16_size) {
                    // dword group
                    random_group = ig_32[pool - ig_16_size];
                    random_tmp   = UR(3);
                    index_0      = random_group->indexes[random_tmp];
                    index_1      = random_group->indexes[random_tmp + 1];
                } else {
                    // qword group
                    random_group = ig_64[pool - ig_32_size - ig_16_size];
                    random_tmp   = UR(7);
                    index_0      = random_group->indexes[random_tmp];
                    index_1      = random_group->indexes[random_tmp + 1];
                }

                if (UR(2)) {
                    tmp     = index_0;
                    index_0 = index_1;
                    index_1 = tmp;
                }
                short val = (tmp_input[index_1] << 8) | tmp_input[index_0];
                val += UR(35) + 1;
                tmp_input[index_0] = val_0;
                tmp_input[index_1] = val_1;
                break;
            }
            case 8: {
                // set interesting dword
                unsigned pool = UR(ig_32_size + ig_64_size);
                if (pool < ig_32_size) {
                    // dword group
                    random_group = ig_32[pool];
                    index_0      = random_group->indexes[0];
                    index_1      = random_group->indexes[1];
                    index_2      = random_group->indexes[2];
                    index_3      = random_group->indexes[3];
                } else {
                    // qword group
                    random_group = ig_64[pool - ig_32_size];
                    random_tmp   = UR(5);
                    index_0      = random_group->indexes[random_tmp];
                    index_1      = random_group->indexes[random_tmp + 1];
                    index_2      = random_group->indexes[random_tmp + 2];
                    index_3      = random_group->indexes[random_tmp + 3];
                }

                int interesting_32 =
                    interesting32[UR(sizeof(interesting32) / sizeof(int))];
                val_0 = interesting_32 & 0xff;
                val_1 = (interesting_32 >> 8) & 0xff;
                val_2 = (interesting_32 >> 16) & 0xff;
                val_3 = (interesting_32 >> 24) & 0xff;
                if (UR(2)) {
                    tmp     = index_0;
                    index_0 = index_3;
                    index_3 = tmp;

                    tmp     = index_2;
                    index_2 = index_3;
                    index_3 = tmp;
                }
                tmp_input[index_0] = val_0;
                tmp_input[index_1] = val_1;
                tmp_input[index_2] = val_2;
                tmp_input[index_3] = val_3;
                break;
            }
            case 9: {
                // random subtract dword
                unsigned pool = UR(ig_32_size + ig_64_size);
                if (pool < ig_32_size) {
                    // dword group
                    random_group = ig_32[pool];
                    index_0      = random_group->indexes[0];
                    index_1      = random_group->indexes[1];
                    index_2      = random_group->indexes[2];
                    index_3      = random_group->indexes[3];
                } else {
                    // qword group
                    random_group = ig_64[pool - ig_32_size];
                    random_tmp   = UR(5);
                    index_0      = random_group->indexes[random_tmp];
                    index_1      = random_group->indexes[random_tmp + 1];
                    index_2      = random_group->indexes[random_tmp + 2];
                    index_3      = random_group->indexes[random_tmp + 3];
                }
                if (UR(2)) {
                    tmp     = index_0;
                    index_0 = index_3;
                    index_3 = tmp;

                    tmp     = index_2;
                    index_2 = index_3;
                    index_3 = tmp;
                }

                int val = (tmp_input[index_3] << 24) |
                          (tmp_input[index_2] << 16) |
                          (tmp_input[index_1] << 8) | tmp_input[index_0];
                val -= UR(35) + 1;
                tmp_input[index_0] = val & 0xff;
                tmp_input[index_1] = (val >> 8) & 0xff;
                tmp_input[index_2] = (val >> 16) & 0xff;
                tmp_input[index_3] = (val >> 24) & 0xff;
                break;
            }
            case 10: {
                // random add dword
                unsigned pool = UR(ig_32_size + ig_64_size);
                if (pool < ig_32_size) {
                    // dword group
                    random_group = ig_32[pool];
                    index_0      = random_group->indexes[0];
                    index_1      = random_group->indexes[1];
                    index_2      = random_group->indexes[2];
                    index_3      = random_group->indexes[3];
                } else {
                    // qword group
                    random_group = ig_64[pool - ig_32_size];
                    random_tmp   = UR(5);
                    index_0      = random_group->indexes[random_tmp];
                    index_1      = random_group->indexes[random_tmp + 1];
                    index_2      = random_group->indexes[random_tmp + 2];
                    index_3      = random_group->indexes[random_tmp + 3];
                }
                if (UR(2)) {
                    tmp     = index_0;
                    index_0 = index_3;
                    index_3 = tmp;

                    tmp     = index_2;
                    index_2 = index_3;
                    index_3 = tmp;
                }

                int val = (tmp_input[index_3] << 24) |
                          (tmp_input[index_2] << 16) |
                          (tmp_input[index_1] << 8) | tmp_input[index_0];
                val += UR(35) + 1;
                tmp_input[index_0] = val & 0xff;
                tmp_input[index_1] = (val >> 8) & 0xff;
                tmp_input[index_2] = (val >> 16) & 0xff;
                tmp_input[index_3] = (val >> 24) & 0xff;
                break;
            }
            default: {
                assert(0 && "havoc default case");
            }
        }
        // do evaluate
        if (__evaluate_branch_query(ctx, query, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->testcase_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[havoc L5] "
                       "Query is SAT\n");
#endif
            ctx->stats.L5_havoc++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            havoc_res   = 1;
        }
    }

    free(testcase_copy);
    free(indexes);
    free(ig_16);
    free(ig_32);
    free(ig_64);
    if (havoc_res)
        return havoc_res;

    // REMEMBER if more phases, tmp_input must be restored!

L6:
    return 0;
}

int z3fuzz_query_check_light(fuzzy_ctx_t* ctx, Z3_ast query,
                             Z3_ast                branch_condition,
                             unsigned char const** proof,
                             unsigned long*        proof_size)
{
    Z3_inc_ref(ctx->z3_ctx, query);
    Z3_inc_ref(ctx->z3_ctx, branch_condition);
    int res =
        __query_check_light(ctx, query, branch_condition, proof, proof_size);
    Z3_dec_ref(ctx->z3_ctx, query);
    Z3_dec_ref(ctx->z3_ctx, branch_condition);
    return res;
}

void z3fuzz_add_assignment(fuzzy_ctx_t* ctx, int idx, Z3_ast assignment_value)
{
    if (idx >= ctx->size_assignments) {
        unsigned old_size     = ctx->size_assignments;
        ctx->size_assignments = (idx + 1) * 3 / 2;
        ctx->assignments      = (Z3_ast*)realloc(
            ctx->assignments, sizeof(Z3_ast) * ctx->size_assignments);
        assert(ctx->assignments != NULL &&
               "z3fuzz_add_assignment() failed realloc");

        // set to zero the new memory
        memset(ctx->assignments + old_size, 0,
               ctx->size_assignments - old_size);
    }
    Z3_inc_ref(ctx->z3_ctx, assignment_value);
    ctx->assignments[idx] = assignment_value;

    // im assuming that assignment_value is a BV
    unsigned char assignment_size = Z3_get_bv_sort_size(
        ctx->z3_ctx, Z3_get_sort(ctx->z3_ctx, assignment_value));

    unsigned old_len = ctx->testcases.data[0].values_len;

    testcase_t* testcase;
    unsigned    i;
    for (i = 0; i < ctx->testcases.size; ++i) {
        testcase = &ctx->testcases.data[i];

        unsigned long assignment_value_concrete =
            ctx->model_eval(ctx->z3_ctx, assignment_value, testcase->values,
                            testcase->value_sizes, testcase->values_len);

        if (testcase->values_len <= idx) {
            testcase->values_len = (idx + 1) * 3 / 2;
            testcase->values     = (unsigned long*)realloc(
                testcase->values, sizeof(unsigned long) * testcase->values_len);
            testcase->value_sizes = (unsigned char*)realloc(
                testcase->value_sizes,
                sizeof(unsigned char) * testcase->values_len);
            testcase->z3_values = (Z3_ast*)realloc(
                testcase->z3_values, sizeof(Z3_ast) * testcase->values_len);
        }

        testcase->value_sizes[idx] = assignment_size;
        testcase->values[idx]      = assignment_value_concrete;
        testcase->z3_values[idx] =
            Z3_mk_unsigned_int(ctx->z3_ctx, assignment_value_concrete,
                               Z3_mk_bv_sort(ctx->z3_ctx, assignment_size));

        testcase->values_len =
            (testcase->values_len > idx + 1) ? testcase->values_len : idx + 1;
    }

    if (old_len < ctx->testcases.data[0].values_len) {
        tmp_input = (unsigned long*)realloc(
            tmp_input, sizeof(unsigned long) * ctx->testcases.data[0].values_len);
        assert(tmp_input != 0 && "z3fuzz_add_assignment - failed realloc");
    }
}

static int compare_ulong(const void* v1, const void* v2)
{
    return *(unsigned long*)v1 - *(unsigned long*)v2;
}

static inline unsigned long
__minimize_maximize_inner(fuzzy_ctx_t* ctx, Z3_ast pi,
                          Z3_ast                to_maximize_minimize,
                          unsigned char const** out_values, unsigned is_max)
{
    __reset_ast_data();
    __detect_involved_inputs(ctx, to_maximize_minimize, &ast_data);

    testcase_t*   current_testcase = &ctx->testcases.data[0];
    unsigned long max_min          = ctx->model_eval(
        ctx->z3_ctx, to_maximize_minimize, tmp_input,
        current_testcase->value_sizes, current_testcase->values_len);
    unsigned long tmp;
    unsigned long original_byte, max_min_byte, i, j;
    ulong*        p;
    unsigned long num_indexes = ast_data.indexes.size;
    unsigned long indexes_array[num_indexes];

    i = 0;
    set_reset_iter__ulong(&ast_data.indexes, 0);
    while (set_iter_next__ulong(&ast_data.indexes, 0, &p))
        indexes_array[i++] = *p;
    qsort(indexes_array, num_indexes, sizeof(unsigned long), compare_ulong);

    for (j = 0; j < num_indexes; ++j) {
        p             = &indexes_array[j];
        original_byte = current_testcase->values[*p];
        max_min_byte  = current_testcase->values[*p];

        for (i = 0; i < 256; ++i) {
            if (i == original_byte)
                continue;

            tmp_input[*p] = (unsigned long)i;
            if (!ctx->model_eval(ctx->z3_ctx, pi, tmp_input,
                                 current_testcase->value_sizes,
                                 current_testcase->values_len))
                continue;

            tmp = ctx->model_eval(ctx->z3_ctx, to_maximize_minimize, tmp_input,
                                  current_testcase->value_sizes,
                                  current_testcase->values_len);
            if ((is_max && tmp > max_min) || (!is_max && tmp < max_min)) {
                max_min_byte = i;
                max_min      = tmp;
            }
        }
        tmp_input[*p] = (unsigned long)max_min_byte;
    }

    __vals_long_to_char(tmp_input, tmp_proof, current_testcase->testcase_len);
    *out_values = tmp_proof;
    return max_min;
}

unsigned long z3fuzz_maximize(fuzzy_ctx_t* ctx, Z3_ast pi, Z3_ast to_maximize,
                              unsigned char const** out_values,
                              unsigned long*        out_len)
{
    // greedy - maximize one byte at a time
    *out_len = ctx->testcases.data[0].testcase_len;
    return __minimize_maximize_inner(ctx, pi, to_maximize, out_values, 1);
}

unsigned long z3fuzz_minimize(fuzzy_ctx_t* ctx, Z3_ast pi, Z3_ast to_minimize,
                              unsigned char const** out_values,
                              unsigned long*        out_len)
{
    // greedy - minimize one byte at a time
    *out_len = ctx->testcases.data[0].testcase_len;
    return __minimize_maximize_inner(ctx, pi, to_minimize, out_values, 0);
}

void z3fuzz_notify_constraint(fuzzy_ctx_t* ctx, Z3_ast constraint)
{
    // this is a visit of the AST of the constraint... Too slow? I don't know
#ifdef SKIP_NOTIFY
    return;
#endif
    ctx->stats.num_univocally_defined +=
        __check_univocally_defined(ctx, constraint, &ast_data);
}

void z3fuzz_dump_proof(fuzzy_ctx_t* ctx, const char* filename,
                       unsigned char const* proof, unsigned long proof_size)
{
    FILE* fp = fopen(filename, "w");
    assert(fp != NULL && "z3fuzz_dump_proof() open failed");

    Z3FUZZ_LOG("dumping proof in %s\n", filename);

    unsigned long i;
    for (i = 0; i < proof_size; i++) {
        fwrite(&proof[i], sizeof(char), 1, fp);
    }
    fclose(fp);
}

unsigned long z3fuzz_evaluate_expression(fuzzy_ctx_t* ctx, Z3_ast value,
                                         unsigned char* values)
{
    __vals_char_to_long(values, tmp_input, ctx->testcases.data[0].values_len);

    unsigned long res = ctx->model_eval(ctx->z3_ctx, value, tmp_input,
                                        ctx->testcases.data[0].value_sizes,
                                        ctx->testcases.data[0].values_len);
    return res;
}

#if Z3_VERSION <= 451
unsigned long z3fuzz_evaluate_expression_z3(fuzzy_ctx_t* ctx, Z3_ast query,
                                            Z3_ast* values)
{
    Z3_ast solution =
        Z3_substitute(ctx->z3_ctx, query, ctx->n_symbols, ctx->symbols, values);
    solution = Z3_simplify(ctx->z3_ctx, solution);

    if (Z3_get_ast_kind(ctx->z3_ctx, solution) == Z3_NUMERAL_AST) {
        long long unsigned int res;
        Z3_bool successGet = Z3_get_numeral_uint64(ctx->z3_ctx, solution, &res);
        assert(successGet == Z3_TRUE &&
               "z3fuzz_evaluate_expression_z3() failed to get "
               "constant");
        return res;
    } else
        return Z3_get_bool_value(ctx->z3_ctx, solution) == Z3_L_TRUE ? 1UL
                                                                     : 0UL;
}
#else
unsigned long z3fuzz_evaluate_expression_z3(fuzzy_ctx_t* ctx, Z3_ast query,
                                            Z3_ast* values)
{
    // evaluate query using [input <- input_val] as interpretation

    // build a model and assign an interpretation for the input symbols
    unsigned long res;
    Z3_model z3_m = Z3_mk_model(ctx->z3_ctx);
    Z3_model_inc_ref(ctx->z3_ctx, z3_m);
    testcase_t* current_testcase = &ctx->testcases.data[0];

    unsigned i;
    for (i = 0; i < current_testcase->values_len; ++i) {
        unsigned int index = i;
        Z3_sort sort =
            Z3_mk_bv_sort(ctx->z3_ctx, current_testcase->value_sizes[i]);
        Z3_symbol s = Z3_mk_int_symbol(ctx->z3_ctx, index);
        Z3_func_decl decl = Z3_mk_func_decl(ctx->z3_ctx, s, 0, NULL, sort);
        Z3_add_const_interp(ctx->z3_ctx, z3_m, decl, values[index]);
    }

    // evaluate the query in the model
    Z3_ast solution;
    Z3_bool successfulEval =
        Z3_model_eval(ctx->z3_ctx, z3_m, query, Z3_TRUE, &solution);
    assert(successfulEval && "Failed to evaluate model");

    Z3_model_dec_ref(ctx->z3_ctx, z3_m);
    if (Z3_get_ast_kind(ctx->z3_ctx, solution) == Z3_NUMERAL_AST) {
        Z3_bool successGet = Z3_get_numeral_uint64(ctx->z3_ctx, solution, &res);
        assert(successGet == Z3_TRUE &&
               "z3fuzz_evaluate_expression_z3() failed to get "
               "constant");
    } else
        res = Z3_get_bool_value(ctx->z3_ctx, solution) == Z3_L_TRUE ? 1UL : 0UL;
    Z3_dec_ref(ctx->z3_ctx, solution);
    return res;
}
#endif
