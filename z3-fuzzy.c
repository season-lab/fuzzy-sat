#include <assert.h>
#include <fcntl.h>
#include <stdlib.h>
#include <unistd.h>
#include "utility/gradient_descend.h"
#include "z3-fuzzy.h"

#ifndef likely
#define likely(x) __builtin_expect(!!(x), 1)
#endif
#ifndef unlikely
#define unlikely(x) __builtin_expect(!!(x), 0)
#endif

#define Z3FUZZ_LOG(x...) fprintf(stderr, "[z3fuzz] " x)
#define FLIP_BIT(_var, _idx) ((_var) ^ (1 << (_idx)));

#define rightmost_set_bit(x) ((x) != 0 ? __builtin_ctzl(x) : -1)
#define leftmost_set_bit(x) ((x) != 0 ? (63 - __builtin_clzl(x)) : -1)

// #define PRINT_SAT
// #define PRINT_NUM_EVALUATE
// #define DEBUG_CHECK_LIGHT
// #define DEBUG_DETECT_GROUP

// #define USE_MD5_HASH

#define USE_AFL_DET_GROUPS

static int log_query_stats = 0;
static int skip_notify     = 0;

static int skip_reuse                   = 1;
static int skip_input_to_state          = 0;
static int skip_input_to_state_extended = 0;
static int skip_brute_force             = 0;
static int skip_gradient_descend        = 0;

static int skip_afl_deterministic          = 0;
static int skip_afl_det_single_walking_bit = 0;
static int skip_afl_det_two_walking_bit    = 0;
static int skip_afl_det_four_walking_bit   = 0;
static int skip_afl_det_byte_flip          = 0;
static int skip_afl_det_arith8             = 0;
static int skip_afl_det_int8               = 0;
static int skip_afl_det_flip_short         = 0;
static int skip_afl_det_arith16            = 0;
static int skip_afl_det_int16              = 0;
static int skip_afl_det_flip_int           = 0;
static int skip_afl_det_arith32            = 0;
static int skip_afl_det_int32              = 0;
static int skip_afl_det_flip_long          = 0;
static int skip_afl_det_arith64            = 0;
static int skip_afl_det_int64              = 0;

static int skip_afl_havoc         = 1;
static int use_greedy_mamin       = 0;
static int check_unnecessary_eval = 0;

#ifdef USE_MD5_HASH
#include "utility/md5.h"
#else
#include "utility/xxhash/xxh3.h"
#endif

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
    unsigned      op_input_to_state;
    index_group_t input_to_state_group;
    unsigned long input_to_state_const;
    unsigned long query_size;

    processed_set_t processed_set;
    index_groups_t  index_groups;
    indexes_t       indexes;
    values_t        values;
} ast_data_t;

static unsigned long* tmp_input     = NULL;
static unsigned char* tmp_proof     = NULL;
static unsigned char* tmp_opt_proof = NULL;
static int            opt_found     = 0;
static ast_data_t     ast_data      = {0};

typedef ast_data_t* ast_data_ptr;
#define DICT_DATA_T ast_data_ptr
#include <dict.h>

static char* query_log_filename = "/tmp/fuzzy-log-info.csv";
FILE*        query_log;

static char  interesting8[]  = {-128, -1, 0, 1, 16, 32, 64, 100, 127};
static short interesting16[] = {-32768, -129, 128,   255,  256, 512, 1000,
                                1024,   4096, 32767, -128, -1,  0,   1,
                                16,     32,   64,    100,  127};
static int   interesting32[] = {
    -2147483648, -100663046, -32769, 32768, 65535, 65536, 100663045,
    2147483647,  -32768,     -129,   128,   255,   256,   512,
    1000,        1024,       4096,   32767, -128,  -1,    0,
    1,           16,         32,     64,    100,   127};

static long interesting64[] = {-9223372036854775807,
                               9223372036854775807,
                               -2147483648,
                               -100663046,
                               -32769,
                               32768,
                               65535,
                               65536,
                               100663045,
                               2147483647,
                               -32768,
                               -129,
                               128,
                               255,
                               256,
                               512,
                               1000,
                               1024,
                               4096,
                               32767,
                               -128,
                               -1,
                               0,
                               1,
                               16,
                               32,
                               64,
                               100,
                               127};

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

// ********* gradient stuff *********
static void __reset_ast_data();
static void detect_involved_inputs_wrapper(fuzzy_ctx_t* ctx, Z3_ast v,
                                           ast_data_t* data);

typedef struct mapping_subel_t {
    unsigned      idx;
    unsigned      shift;
    unsigned long mask;
} mapping_subel_t;

typedef struct mapping_el_t {
    mapping_subel_t subels[8];
    unsigned        n;
} mapping_el_t;

typedef struct eval_wapper_ctx_t {
    char           check_pi_eval;
    unsigned long* input;
    mapping_el_t*  mapping;
    unsigned       mapping_size;
    unsigned       ast_sort_size;
    Z3_ast         pi;
    Z3_ast         ast;
    fuzzy_ctx_t*   fctx;
} eval_wapper_ctx_t;

static eval_wapper_ctx_t* eval_ctx;
static eval_wapper_ctx_t* multi_eval_ctx;
static unsigned           multi_eval_n;

void eval_set_ctx(eval_wapper_ctx_t* c) { eval_ctx = c; }
void eval_multi_set_ctx(eval_wapper_ctx_t* c, unsigned n)
{
    multi_eval_ctx = c;
    multi_eval_n   = n;
}

static void __gd_fix_tmp_input(unsigned long* x)
{
    unsigned i, j;
    for (i = 0; i < eval_ctx->mapping_size; ++i) {
        mapping_el_t* mel = &eval_ctx->mapping[i];
        for (j = 0; j < mel->n; ++j) {
            mapping_subel_t* sel   = &mel->subels[j];
            unsigned long    value = (x[i] & sel->mask) >> sel->shift;
            tmp_input[sel->idx]    = value & 0xff;
        }
    }
}

static void __gd_restore_tmp_input(testcase_t* t)
{
    unsigned i, j;
    for (i = 0; i < eval_ctx->mapping_size; ++i) {
        mapping_el_t* mel = &eval_ctx->mapping[i];
        for (j = 0; j < mel->n; ++j) {
            mapping_subel_t* sel = &mel->subels[j];
            tmp_input[sel->idx]  = t->values[sel->idx];
        }
    }
}

static unsigned long __gd_eval(unsigned long* x)
{
    testcase_t* seed_testcase = &eval_ctx->fctx->testcases.data[0];
    __gd_fix_tmp_input(x);

    if (eval_ctx->check_pi_eval) {
        unsigned long pi_eval = eval_ctx->fctx->model_eval(
            eval_ctx->fctx->z3_ctx, eval_ctx->pi, x, seed_testcase->value_sizes,
            seed_testcase->values_len);

        if (!pi_eval)
            return 0xffffffffffffffff;
    }

    unsigned long res = eval_ctx->fctx->model_eval(
        eval_ctx->fctx->z3_ctx, eval_ctx->ast, tmp_input,
        seed_testcase->value_sizes, seed_testcase->values_len);
    eval_ctx->fctx->stats.num_evaluate++;
    return res;
}

__attribute__((unused)) static unsigned long __multi_eval(unsigned long* x,
                                                          unsigned       i)
{
    assert(i < multi_eval_n && "eval multi overflow");
    eval_set_ctx(&multi_eval_ctx[i]);
    return __gd_eval(x);
}

static int __gd_init_eval(fuzzy_ctx_t* ctx, Z3_ast pi, Z3_ast expr,
                          char check_pi_eval, char must_initialize_ast,
                          eval_wapper_ctx_t* out_ctx)
{
    out_ctx->fctx          = ctx;
    out_ctx->pi            = pi;
    out_ctx->ast           = expr;
    out_ctx->check_pi_eval = check_pi_eval;

    Z3_inc_ref(ctx->z3_ctx, out_ctx->ast);
    Z3_inc_ref(ctx->z3_ctx, out_ctx->pi);

    Z3_sort bv_sort = Z3_get_sort(ctx->z3_ctx, expr);
    assert(Z3_get_sort_kind(ctx->z3_ctx, bv_sort) == Z3_BV_SORT &&
           "gd works with bitvectors");
    out_ctx->ast_sort_size = Z3_get_bv_sort_size(ctx->z3_ctx, bv_sort);

    if (must_initialize_ast) {
        __reset_ast_data();
        detect_involved_inputs_wrapper(ctx, expr, &ast_data);

        if (ast_data.indexes.size == 0)
            return 0; // no index!
    }

    out_ctx->mapping_size = ast_data.index_groups.size;
    out_ctx->mapping =
        (mapping_el_t*)malloc(sizeof(mapping_el_t) * out_ctx->mapping_size);
    out_ctx->input =
        (unsigned long*)malloc(sizeof(unsigned long) * out_ctx->mapping_size);

    unsigned       idx = 0;
    index_group_t* g;
    set_reset_iter__index_group_t(&ast_data.index_groups, 0);
    while (set_iter_next__index_group_t(&ast_data.index_groups, 0, &g)) {
        int i;
        out_ctx->mapping[idx].n = g->n;
        for (i = 0; i < g->n; ++i) {
            unsigned fixed_i                            = g->n - i - 1;
            out_ctx->mapping[idx].subels[fixed_i].idx   = g->indexes[i];
            out_ctx->mapping[idx].subels[fixed_i].shift = fixed_i * 8;
            out_ctx->mapping[idx].subels[fixed_i].mask  = 0xff << (fixed_i * 8);

            out_ctx->input[idx] |= tmp_input[g->indexes[i]] << (fixed_i * 8);
        }
        idx++;
    }

    // groups can overlap... Detect it and fallback to byte-byte method

    // unsigned i = 0;
    // ulong*   p;
    // set_reset_iter__ulong(&ast_data.indexes, 0);
    // while (set_iter_next__ulong(&ast_data.indexes, 0, &p)) {
    //     __glob_gd_mapping[i] = *p;
    //     __glob_gd_input[i++] = tmp_input[*p];
    // }

    return 1;
}

static void __gd_free_eval(eval_wapper_ctx_t* eval_ctx)
{
    Z3_dec_ref(eval_ctx->fctx->z3_ctx, eval_ctx->pi);
    Z3_dec_ref(eval_ctx->fctx->z3_ctx, eval_ctx->ast);

    free(eval_ctx->mapping);
    free(eval_ctx->input);
}

static int __gradient_transf_init(Z3_context ctx, Z3_ast expr, Z3_ast* out_exp)
{
    assert(Z3_get_ast_kind(ctx, expr) == Z3_APP_AST &&
           "__gradient_transf_init expects an APP argument");

    Z3_app       app       = Z3_to_app(ctx, expr);
    Z3_func_decl decl      = Z3_get_app_decl(ctx, app);
    Z3_decl_kind decl_kind = Z3_get_decl_kind(ctx, decl);

    int    is_not = 0;
    Z3_ast arg    = expr;
    while (decl_kind == Z3_OP_NOT) {
        arg       = Z3_get_app_arg(ctx, app, 0);
        app       = Z3_to_app(ctx, arg);
        decl      = Z3_get_app_decl(ctx, app);
        decl_kind = Z3_get_decl_kind(ctx, decl);
        is_not    = !is_not;
    }

    assert(Z3_get_app_num_args(ctx, app) == 2 &&
           "__gradient_transf_init requires a binary APP");

    Z3_ast args[2] = {0};
    Z3_inc_ref(ctx, arg);
    Z3_ast arg1 = Z3_get_app_arg(ctx, app, 0);
    Z3_inc_ref(ctx, arg1);
    Z3_ast arg2 = Z3_get_app_arg(ctx, app, 1);
    Z3_inc_ref(ctx, arg2);
    Z3_dec_ref(ctx, arg);

    Z3_sort arg_sort = Z3_get_sort(ctx, arg1);
    if (Z3_get_sort_kind(ctx, arg_sort) != Z3_BV_SORT)
        return 0;
    unsigned sort_size = Z3_get_bv_sort_size(ctx, arg_sort);
    assert(sort_size > 1 && "__gradient_transf_init unexpected sort size");

    if (sort_size < 64) {
        int is_unsigned = 0;
        if (decl_kind == Z3_OP_UGT || decl_kind == Z3_OP_UGEQ ||
            decl_kind == Z3_OP_ULT || decl_kind == Z3_OP_ULEQ)
            is_unsigned = 1;

        if (is_unsigned) {
            Z3_ast tmp1 = arg1;
            Z3_ast tmp2 = arg2;
            arg1        = Z3_mk_zero_ext(ctx, 64 - sort_size, tmp1);
            Z3_inc_ref(ctx, arg1);
            arg2 = Z3_mk_zero_ext(ctx, 64 - sort_size, tmp2);
            Z3_inc_ref(ctx, arg2);
            Z3_dec_ref(ctx, tmp1);
            Z3_dec_ref(ctx, tmp2);
            sort_size = 64;
        } else {
            Z3_ast tmp1 = arg1;
            Z3_ast tmp2 = arg2;
            arg1        = Z3_mk_sign_ext(ctx, 64 - sort_size, tmp1);
            Z3_inc_ref(ctx, arg1);
            arg2 = Z3_mk_sign_ext(ctx, 64 - sort_size, tmp2);
            Z3_inc_ref(ctx, arg2);
            Z3_dec_ref(ctx, tmp1);
            Z3_dec_ref(ctx, tmp2);
            sort_size = 64;
        }
    }

    Z3_ast res;

PRE_SWITCH:
    switch (decl_kind) {
        case Z3_OP_SGT:
        case Z3_OP_SGEQ:
        case Z3_OP_UGT:
        case Z3_OP_UGEQ: { // arg1 > arg2 => arg2 - arg1
            if (is_not) {
                is_not    = 0;
                decl_kind = Z3_OP_SLT;
                goto PRE_SWITCH;
            }
            args[0] = arg2;
            args[1] = arg1;
            res     = Z3_mk_bvsub(ctx, args[0], args[1]);
            Z3_inc_ref(ctx, res);
            break;
        }
        case Z3_OP_SLT:
        case Z3_OP_SLEQ:
        case Z3_OP_ULT:
        case Z3_OP_ULEQ: { // arg1 < arg2 => arg1 - arg2
            if (is_not) {
                is_not    = 0;
                decl_kind = Z3_OP_SGT;
                goto PRE_SWITCH;
            }
            args[0] = arg1;
            args[1] = arg2;
            res     = Z3_mk_bvsub(ctx, args[0], args[1]);
            Z3_inc_ref(ctx, res);
            break;
        }
        case Z3_OP_EQ: { // arg1 == arg2 =>   abs(arg1 - arg2)
                         // arg1 != arg2 => - abs(arg1 - arg2)
            args[0] = arg1;
            args[1] = arg2;

            Z3_ast cond = Z3_mk_bvsgt(ctx, args[0], args[1]);
            Z3_inc_ref(ctx, cond);
            Z3_ast ift = Z3_mk_bvsub(ctx, args[0], args[1]);
            Z3_inc_ref(ctx, ift);
            Z3_ast iff = Z3_mk_bvsub(ctx, args[1], args[0]);
            Z3_inc_ref(ctx, iff);

            assert(Z3_get_sort_kind(ctx, Z3_get_sort(ctx, cond)) ==
                       Z3_BOOL_SORT &&
                   "not bool sort");
            Z3_ast ite = Z3_mk_ite(ctx, cond, ift, iff);
            Z3_inc_ref(ctx, ite);
            Z3_dec_ref(ctx, cond);
            Z3_dec_ref(ctx, ift);
            Z3_dec_ref(ctx, iff);

            if (is_not) {
                Z3_ast zero =
                    Z3_mk_unsigned_int64(ctx, 0, Z3_mk_bv_sort(ctx, sort_size));
                Z3_inc_ref(ctx, zero);
                res = Z3_mk_bvsub(ctx, zero, ite);
                Z3_inc_ref(ctx, res);
                Z3_dec_ref(ctx, ite);
                Z3_dec_ref(ctx, zero);
            } else
                res = ite;
            break;
        }

        default:
            assert(0 && "__gradient_transf_init unknown decl kind");
    }

    Z3_inc_ref(ctx, res);
    *out_exp = res;
    return 1;
}
// **********************************

static void __init_ast_data(ast_data_t* ast_data)
{
    set_init__digest_t(&ast_data->processed_set, &digest_64bit_hash,
                       &digest_equals);
    set_init__index_group_t(&ast_data->index_groups, &index_group_hash,
                            &index_group_equals);
    set_init__ulong(&ast_data->indexes, &index_hash, &index_equals);
    da_init__ulong(&ast_data->values);
}

static void __free_ast_data(ast_data_t* ast_data)
{
    set_free__digest_t(&ast_data->processed_set);
    set_free__index_group_t(&ast_data->index_groups);
    set_free__ulong(&ast_data->indexes);
    da_free__ulong(&ast_data->values, NULL);
}

static void __free_ast_data_ptr(ast_data_ptr* ast_data)
{
    __free_ast_data(*ast_data);
    free(*ast_data);
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

static void env_get_or_die(int* env_var, char* value)
{
    if (value == NULL)
        return;

    if (value[0] == '0')
        *env_var = 0;
    else if (value[0] == '1')
        *env_var = 1;
    else
        assert(0 && "environment config value must be '0' or '1'");
}

static void init_config_params()
{
    env_get_or_die(&log_query_stats, getenv("Z3FUZZ_LOG_QUERY_STATS"));
    env_get_or_die(&skip_notify, getenv("Z3FUZZ_SKIP_NOTIFY"));
    env_get_or_die(&skip_reuse, getenv("Z3FUZZ_SKIP_REUSE"));
    env_get_or_die(&skip_input_to_state, getenv("Z3FUZZ_SKIP_INPUT_TO_STATE"));
    env_get_or_die(&skip_input_to_state_extended,
                   getenv("Z3FUZZ_SKIP_INPUT_TO_STATE_EXTENDED"));
    env_get_or_die(&skip_brute_force, getenv("Z3FUZZ_SKIP_BRUTE_FORCE"));
    env_get_or_die(&skip_afl_deterministic,
                   getenv("Z3FUZZ_SKIP_DETERMINISTIC"));
    env_get_or_die(&skip_afl_det_single_walking_bit,
                   getenv("Z3FUZZ_SKIP_SINGLE_WALKING_BIT"));
    env_get_or_die(&skip_afl_det_two_walking_bit,
                   getenv("Z3FUZZ_SKIP_TWO_WALKING_BIT"));
    env_get_or_die(&skip_afl_det_four_walking_bit,
                   getenv("Z3FUZZ_SKIP_FOUR_WALKING_BIT"));
    env_get_or_die(&skip_afl_det_byte_flip, getenv("Z3FUZZ_SKIP_BYTE_FLIP"));
    env_get_or_die(&skip_afl_det_arith8, getenv("Z3FUZZ_SKIP_ARITH8"));
    env_get_or_die(&skip_afl_det_int8, getenv("Z3FUZZ_SKIP_INT8"));
    env_get_or_die(&skip_afl_det_flip_short, getenv("Z3FUZZ_SKIP_FLIP_SHORT"));
    env_get_or_die(&skip_afl_det_arith16, getenv("Z3FUZZ_SKIP_ARITH16"));
    env_get_or_die(&skip_afl_det_int16, getenv("Z3FUZZ_SKIP_INT16"));
    env_get_or_die(&skip_afl_det_flip_int, getenv("Z3FUZZ_SKIP_FLIP_INT"));
    env_get_or_die(&skip_afl_det_arith32, getenv("Z3FUZZ_SKIP_ARITH32"));
    env_get_or_die(&skip_afl_det_int32, getenv("Z3FUZZ_SKIP_INT32"));
    env_get_or_die(&skip_afl_det_flip_long, getenv("Z3FUZZ_SKIP_FLIP_LONG"));
    env_get_or_die(&skip_afl_det_arith64, getenv("Z3FUZZ_SKIP_ARITH64"));
    env_get_or_die(&skip_afl_det_int64, getenv("Z3FUZZ_SKIP_INT64"));
    env_get_or_die(&skip_afl_havoc, getenv("Z3FUZZ_SKIP_HAVOC"));
    env_get_or_die(&skip_gradient_descend,
                   getenv("Z3FUZZ_SKIP_GRADIENT_DESCEND"));
    env_get_or_die(&use_greedy_mamin, getenv("Z3FUZZ_USE_GREEDY_MAMIN"));
    env_get_or_die(&check_unnecessary_eval,
                   getenv("Z3FUZZ_CHECK_UNNECESSARY_EVAL"));
}

void z3fuzz_init(fuzzy_ctx_t* fctx, Z3_context ctx, char* seed_filename,
                 char* testcase_path,
                 uint64_t (*model_eval)(Z3_context, Z3_ast, uint64_t*, uint8_t*,
                                        size_t))
{
    init_config_params();
    memset((void*)&fctx->stats, 0, sizeof(fuzzy_stats_t));

    Z3_set_ast_print_mode(ctx, Z3_PRINT_SMTLIB2_COMPLIANT);

    dev_urandom_fd = open("/dev/urandom", O_RDONLY);
    if (dev_urandom_fd < 0)
        assert(0 && "Unable to open /dev/urandom");

    if (log_query_stats) {
        query_log = fopen(query_log_filename, "w");
        fprintf(
            query_log,
            "query size;index size;index group size;is input to state;linear "
            "arith ops;non linear arith ops");
    }

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
    tmp_input     = (unsigned long*)malloc(sizeof(unsigned long) *
                                       current_testcase->values_len);
    tmp_proof     = (unsigned char*)malloc(sizeof(unsigned char) *
                                       current_testcase->testcase_len);
    tmp_opt_proof = (unsigned char*)malloc(sizeof(unsigned char) *
                                           current_testcase->testcase_len);

    fctx->univocally_defined_inputs = (void*)malloc(sizeof(set__ulong));
    set_init__ulong((set__ulong*)fctx->univocally_defined_inputs, &index_hash,
                    &index_equals);

    __init_ast_data(&ast_data);

    fctx->assignment_inputs_cache = malloc(sizeof(dict__ast_data_ptr));
    dict__ast_data_ptr* assignment_inputs_cache =
        (dict__ast_data_ptr*)fctx->assignment_inputs_cache;
    dict_init__ast_data_ptr(assignment_inputs_cache);

    gd_init();
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
    free(tmp_opt_proof);
    tmp_opt_proof = NULL;

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

    __free_ast_data(&ast_data);

    dict__ast_data_ptr* assignment_inputs_cache =
        (dict__ast_data_ptr*)ctx->assignment_inputs_cache;
    dict_free__ast_data_ptr(assignment_inputs_cache, __free_ast_data_ptr);
    free(ctx->assignment_inputs_cache);

    set_free__ulong((set__ulong*)ctx->univocally_defined_inputs);
    free(ctx->univocally_defined_inputs);

    gd_free();

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

static int __check_or_add_digest(set__digest_t* set, unsigned char* values,
                                 unsigned n)
{
    digest_t d;
#ifdef USE_MD5_HASH
    md5((unsigned char*)values, n, d.digest);
#else
    XXH128_hash_t xxd = XXH3_128bits((unsigned char*)values, n);
    d.digest[0]       = xxd.high64 & 0xff;
    d.digest[1]       = (xxd.high64 >> 8) & 0xff;
    d.digest[2]       = (xxd.high64 >> 16) & 0xff;
    d.digest[3]       = (xxd.high64 >> 24) & 0xff;
    d.digest[4]       = xxd.low64 & 0xff;
    d.digest[5]       = (xxd.low64 >> 8) & 0xff;
    d.digest[6]       = (xxd.low64 >> 16) & 0xff;
    d.digest[7]       = (xxd.low64 >> 24) & 0xff;
#endif

    if (set_check__digest_t(set, d))
        return 1;
    set_add__digest_t(set, d);
    return 0;
}

static inline int __evaluate_branch_query(fuzzy_ctx_t* ctx, Z3_ast query,
                                          Z3_ast         branch_condition,
                                          unsigned long* values,
                                          unsigned char* value_sizes,
                                          unsigned long  n_values)
{
    ctx->stats.num_evaluate++;

    if (check_unnecessary_eval)
        if (__check_or_add_digest(&ast_data.processed_set,
                                  (unsigned char*)values,
                                  ctx->n_symbols * sizeof(unsigned long))) {
            return 0;
        }

    int res;
    res = (int)ctx->model_eval(ctx->z3_ctx, branch_condition, values,
                               value_sizes, n_values);
    if (res) {
        if (!opt_found) {
            testcase_t* t = &ctx->testcases.data[0];
            opt_found     = 1;
            __vals_long_to_char(t->values, tmp_opt_proof, t->testcase_len);
        }
        res = (int)ctx->model_eval(ctx->z3_ctx, query, values, value_sizes,
                                   n_values);
    }
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
                case Z3_OP_EXTRACT: {
#ifdef DEBUG_DETECT_GROUP
                    printf("DETECT_GROUP [Z3_OP_EXTRACT]\n");
#endif

                    int prev_n = ig->n;

                    unsigned long hig =
                        Z3_get_decl_int_parameter(ctx->z3_ctx, decl, 0);
                    unsigned long low =
                        Z3_get_decl_int_parameter(ctx->z3_ctx, decl, 1);
#ifdef DEBUG_DETECT_GROUP
                    printf("hig: %lu, low: %lu, prev_n: %d\n", hig, low,
                           prev_n);
#endif

                    // recursive call
                    res = __detect_input_group(
                        ctx, Z3_get_app_arg(ctx->z3_ctx, app, 0), ig);
                    if (res == 0)
                        break;

                    int next_n = ig->n;
#ifdef DEBUG_DETECT_GROUP
                    printf("next_n: %d\n", next_n);
                    for (i = 0; i < ig->n; ++i)
                        printf(" @ ig->indexes[%u] = 0x%lx\n", i,
                               ig->indexes[i]);
#endif

                    unsigned bv_width = next_n - prev_n;
                    if (bv_width < hig / 8 + 1) {
                        res = 0;
                        break;
                    }

                    // spill in tmp (little endian)
                    unsigned long tmp[bv_width];
                    for (i = 0; i < bv_width; ++i)
                        tmp[i] = ig->indexes[next_n - i - 1];

                    // move tmp to: ig->indexes + prev_n
                    for (i = low / 8; i <= hig / 8; ++i) {
                        assert(i < bv_width && "extract overflow");
                        ig->indexes[prev_n++] = tmp[i];
                    }
                    ig->n = prev_n;

#ifdef DEBUG_DETECT_GROUP
                    for (i = 0; i < ig->n; ++i)
                        printf(" > ig->indexes[%u] = 0x%lx\n", i,
                               ig->indexes[i]);
#endif
                    break;
                }
                case Z3_OP_BAND: {
#ifdef DEBUG_DETECT_GROUP
                    printf("DETECT_GROUP [Z3_OP_BAND]\n");
#endif
                    // check if one of the two is a constant
                    // recursive call as before
                    if (num_fields != 2) {
                        res = 0;
                        break;
                    }

                    Z3_ast child_1 = Z3_get_app_arg(ctx->z3_ctx, app, 0);
                    Z3_inc_ref(ctx->z3_ctx, child_1);

                    Z3_ast child_2 = Z3_get_app_arg(ctx->z3_ctx, app, 1);
                    Z3_inc_ref(ctx->z3_ctx, child_2);

                    Z3_ast        subexpr = NULL;
                    unsigned long mask;
                    if (Z3_get_ast_kind(ctx->z3_ctx, child_1) ==
                        Z3_NUMERAL_AST) {
                        Z3_bool successGet = Z3_get_numeral_uint64(
                            ctx->z3_ctx, child_1, (uint64_t*)&mask);
                        if (successGet == Z3_FALSE) {
                            res = 0;
                            goto BVAND_EXIT;
                        }
                        subexpr = child_2;
                    } else if (Z3_get_ast_kind(ctx->z3_ctx, child_2) ==
                               Z3_NUMERAL_AST) {
                        Z3_bool successGet = Z3_get_numeral_uint64(
                            ctx->z3_ctx, child_2, (uint64_t*)&mask);
                        if (successGet == Z3_FALSE) {
                            res = 0; // constant is too big
                            goto BVAND_EXIT;
                        }
                        subexpr = child_1;
                    }
                    if (mask == 0) {
                        res = 1; // and with 0 -> no group, it is always 0
                        goto BVAND_EXIT;
                    }

                    int prev_n = ig->n;
#ifdef DEBUG_DETECT_GROUP
                    printf("prev_n: %d\n", prev_n);
#endif

                    // recursive call
                    res = __detect_input_group(ctx, subexpr, ig);
                    if (res == 0)
                        goto BVAND_EXIT;

                    // find rightmost and leftmost set-bit of mask
                    unsigned long low = rightmost_set_bit(mask);
                    unsigned long hig = leftmost_set_bit(mask);

                    int next_n = ig->n;
#ifdef DEBUG_DETECT_GROUP
                    printf("low: %lu, hig: %lu\n", low, hig);
                    printf("next_n: %d\n", next_n);
                    for (i = 0; i < ig->n; ++i)
                        printf(" @ ig->indexes[%u] = 0x%lx\n", i,
                               ig->indexes[i]);
#endif

                    unsigned bv_width = next_n - prev_n;
                    if (bv_width < hig / 8 + 1) {
                        res = 0;
                        goto BVAND_EXIT;
                    }

                    // spill in tmp (little endian)
                    unsigned long* tmp = (unsigned long*)malloc(
                        sizeof(unsigned long) * bv_width);
                    for (i = 0; i < bv_width; ++i)
                        tmp[i] = ig->indexes[next_n - i - 1];

                    // move tmp to: ig->indexes + prev_n
                    for (i = low / 8; i <= hig / 8; ++i) {
                        assert(i < bv_width && "extract overflow");
                        ig->indexes[prev_n++] = tmp[i];
                    }
                    ig->n = prev_n;

#ifdef DEBUG_DETECT_GROUP
                    for (i = 0; i < ig->n; ++i)
                        printf(" > ig->indexes[%u] = 0x%lx\n", i,
                               ig->indexes[i]);
#endif
                    free(tmp);

                BVAND_EXIT:
                    Z3_dec_ref(ctx->z3_ctx, child_1);
                    Z3_dec_ref(ctx->z3_ctx, child_2);
                    break;
                }
                case Z3_OP_BADD:
                case Z3_OP_BOR: {
                    // detect if is an OR/ADD of BSHL
#ifdef DEBUG_DETECT_GROUP
                    printf("DETECT_GROUP [Z3_OP_BADD/Z3_OP_BOR]\n");
#endif

                    res                            = 0;
                    unsigned long shift_mask       = 0;
                    int           op_without_shift = 0;
                    for (i = 0; i < num_fields; ++i) {
                        Z3_ast child = Z3_get_app_arg(ctx->z3_ctx, app, i);
                        if (Z3_get_ast_kind(ctx->z3_ctx, child) == Z3_APP_AST) {
                            Z3_app child_app = Z3_to_app(ctx->z3_ctx, child);
                            Z3_func_decl child_decl =
                                Z3_get_app_decl(ctx->z3_ctx, child_app);
                            if (Z3_get_decl_kind(ctx->z3_ctx, child_decl) ==
                                Z3_OP_BSHL) {
#ifdef DEBUG_DETECT_GROUP
                                printf("> shift\n");
#endif
                                unsigned long shift_val = 0;

                                Z3_ast child_1 =
                                    Z3_get_app_arg(ctx->z3_ctx, child_app, 0);
                                Z3_inc_ref(ctx->z3_ctx, child_1);

                                Z3_ast child_2 =
                                    Z3_get_app_arg(ctx->z3_ctx, child_app, 1);
                                Z3_inc_ref(ctx->z3_ctx, child_2);

                                Z3_ast subexpr = NULL;
                                if (Z3_get_ast_kind(ctx->z3_ctx, child_1) ==
                                    Z3_NUMERAL_AST) {
                                    Z3_bool successGet = Z3_get_numeral_uint64(
                                        ctx->z3_ctx, child_1,
                                        (uint64_t*)&shift_val);
                                    if (!successGet)
                                        res = 0; // constant is too big
                                    else {
                                        subexpr = child_2;
                                        res     = 1;
                                    }

                                } else if (Z3_get_ast_kind(ctx->z3_ctx,
                                                           child_2) ==
                                           Z3_NUMERAL_AST) {
                                    Z3_bool successGet = Z3_get_numeral_uint64(
                                        ctx->z3_ctx, child_2,
                                        (uint64_t*)&shift_val);
                                    if (!successGet)
                                        res = 0; // constant is too big
                                    else {
                                        subexpr = child_1;
                                        res     = 1;
                                    }
                                } else
                                    res = 0;

                                if (!res) {
                                    Z3_dec_ref(ctx->z3_ctx, child_1);
                                    Z3_dec_ref(ctx->z3_ctx, child_2);
                                    break;
                                }

#ifdef DEBUG_DETECT_GROUP
                                printf("> shift val: 0x%016lx\n", shift_val);
#endif

                                if (((0xff << shift_val) & shift_mask) != 0) {
                                    res = 0;
                                    Z3_dec_ref(ctx->z3_ctx, child_1);
                                    Z3_dec_ref(ctx->z3_ctx, child_2);
                                    break;
                                }
                                shift_mask |= 0xff << shift_val;

                                res = __detect_input_group(ctx, subexpr, ig);
                                Z3_dec_ref(ctx->z3_ctx, child_1);
                                Z3_dec_ref(ctx->z3_ctx, child_2);

                                if (!res)
                                    break;
#ifdef DEBUG_DETECT_GROUP
                                printf("> shift OK\n");
#endif
                                continue;
                            }
                        }
                        if (!op_without_shift)
                            op_without_shift = 1;
                        else {
                            res = 0;
                            break;
                        }
#ifdef DEBUG_DETECT_GROUP
                        printf("> op != shift\n");
#endif
                        res = __detect_input_group(ctx, child, ig);
                        if (!res)
                            break;
#ifdef DEBUG_DETECT_GROUP
                        printf("> op != shift OK\n");
#endif
                    }

                    break;
                }
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
                ctx->z3_ctx, child, (uint64_t*)&data->input_to_state_const);
            if (successGet == Z3_FALSE)
                return; // constant is too big
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
    condition_ok =
        __detect_input_group(
            ctx,
            Z3_get_app_arg(ctx->z3_ctx, node_app, const_operand == 1 ? 0 : 1),
            &data->input_to_state_group) &&
        data->input_to_state_group.n > 0;

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

    data->op_input_to_state = op_type;
    data->is_input_to_state = 1;
    return;
}

static void __union_indexes(ast_data_t* dst, ast_data_t* src)
{
    index_group_t* group;
    set_reset_iter__index_group_t(&src->index_groups, 0);
    while (set_iter_next__index_group_t(&src->index_groups, 0, &group)) {
        set_add__index_group_t(&dst->index_groups, *group);
    }

    ulong* p;
    set_reset_iter__ulong(&src->indexes, 0);
    while (set_iter_next__ulong(&src->indexes, 0, &p)) {
        set_add__ulong(&dst->indexes, *p);
    }
}

static void __detect_assignment_involved_inputs(fuzzy_ctx_t* ctx,
                                                unsigned     assignment_idx,
                                                ast_data_t*  data)
{
    dict__ast_data_ptr* assignment_inputs_cache =
        (dict__ast_data_ptr*)ctx->assignment_inputs_cache;

    ast_data_ptr  cached_el;
    ast_data_ptr* cached_el_ptr = dict_get_ref__ast_data_ptr(
        assignment_inputs_cache, (unsigned long)assignment_idx);
    if (cached_el_ptr != NULL) {
        cached_el = *cached_el_ptr;
    } else {
        cached_el = (ast_data_ptr)malloc(sizeof(ast_data_t));
        __init_ast_data(cached_el);
        detect_involved_inputs_wrapper(ctx, ctx->assignments[assignment_idx],
                                       cached_el);
        dict_set__ast_data_ptr(assignment_inputs_cache,
                               (unsigned long)assignment_idx, cached_el);
    }
    __union_indexes(data, cached_el);
}

static void __detect_involved_inputs(fuzzy_ctx_t* ctx, Z3_ast v,
                                     ast_data_t* data,
                                     set__ulong* visited_subtrees)
{
    // visit the AST and collect some data
    // 1. Find "groups" of inputs involved in the AST and store them in
    // 'index_queue'
    // 2. Populate global 'indexes' with encountered indexes

    ulong hash = Z3_get_ast_id(ctx->z3_ctx, v);
    if (set_check__ulong(visited_subtrees, hash))
        return;
    set_add__ulong(visited_subtrees, hash);

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
                case Z3_OP_BAND:
                case Z3_OP_BADD:
                case Z3_OP_BOR:
                case Z3_OP_EXTRACT:
                case Z3_OP_CONCAT: {
                    index_group_t group = {0};
                    if (__detect_input_group(ctx, v, &group) && group.n > 0) {
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

                        __detect_assignment_involved_inputs(ctx, symbol_index,
                                                            data);
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
                default: {
                    break;
                }
            }
            if (num_fields > 0) {
                for (i = 0; i < num_fields; i++) {
                    __detect_involved_inputs(
                        ctx, Z3_get_app_arg(ctx->z3_ctx, app, i), data,
                        visited_subtrees);
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

static void detect_involved_inputs_wrapper(fuzzy_ctx_t* ctx, Z3_ast v,
                                           ast_data_t* data)
{
    set__ulong visited_subtrees;
    set_init__ulong(&visited_subtrees, &index_hash, &index_equals);
    __detect_involved_inputs(ctx, v, data, &visited_subtrees);
    set_free__ulong(&visited_subtrees);
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
                            ctx->z3_ctx, child1, (uint64_t*)&tmp_const);
                        assert(successGet == Z3_TRUE &&
                               "failed to get constant");
                        da_add_item__ulong(&data->values, tmp_const);
                        da_add_item__ulong(&data->values, tmp_const + 1);
                        da_add_item__ulong(&data->values, tmp_const - 1);
                    } else if (Z3_get_ast_kind(ctx->z3_ctx, child2) ==
                               Z3_NUMERAL_AST) {
                        successGet = Z3_get_numeral_uint64(
                            ctx->z3_ctx, child2, (uint64_t*)&tmp_const);
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
                            ctx->z3_ctx, child1, (uint64_t*)&tmp_const);
                        assert(successGet == Z3_TRUE &&
                               "failed to get constant");
                        da_add_item__ulong(&data->values, tmp_const);
                        da_add_item__ulong(&data->values, tmp_const + 1);
                        da_add_item__ulong(&data->values, tmp_const - 1);
                    } else if (Z3_get_ast_kind(ctx->z3_ctx, child2) ==
                               Z3_NUMERAL_AST) {
                        successGet = Z3_get_numeral_uint64(
                            ctx->z3_ctx, child2, (uint64_t*)&tmp_const);
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
    detect_involved_inputs_wrapper(ctx, expr, &ast_data);
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

static inline int __detect_strcmp_pattern(fuzzy_ctx_t* ctx, Z3_ast ast,
                                          unsigned long* values)
{
    /*
        (... whatever
            (concat
                #x0..0
                (ite (= inp_0 const_0) #b1 #b0)
                (ite (= inp_1 const_1) #b1 #b0)
                ...
                (ite (= inp_i const_i) #b1 #b0)))
    */
    Z3_bool     successGet;
    unsigned    i;
    Z3_ast_kind kind = Z3_get_ast_kind(ctx->z3_ctx, ast);
    if (kind != Z3_APP_AST)
        return 0;

    int          res        = 0;
    Z3_app       app        = Z3_to_app(ctx->z3_ctx, ast);
    unsigned     num_fields = Z3_get_app_num_args(ctx->z3_ctx, app);
    Z3_func_decl decl       = Z3_get_app_decl(ctx->z3_ctx, app);
    Z3_decl_kind decl_kind  = Z3_get_decl_kind(ctx->z3_ctx, decl);

    if (decl_kind == Z3_OP_CONCAT) {
        res = 1;
        for (i = 0; i < num_fields; ++i) {
            Z3_ast      child      = Z3_get_app_arg(ctx->z3_ctx, app, i);
            Z3_ast_kind child_kind = Z3_get_ast_kind(ctx->z3_ctx, child);
            if (child_kind == Z3_NUMERAL_AST)
                continue;
            if (child_kind == Z3_APP_AST) {
                Z3_app       child_app = Z3_to_app(ctx->z3_ctx, child);
                Z3_func_decl child_decl =
                    Z3_get_app_decl(ctx->z3_ctx, child_app);
                Z3_decl_kind child_decl_kind =
                    Z3_get_decl_kind(ctx->z3_ctx, child_decl);
                if (child_decl_kind != Z3_OP_ITE) {
                    res = 0;
                    break;
                }
                Z3_ast cond    = Z3_get_app_arg(ctx->z3_ctx, child_app, 0);
                Z3_ast iftrue  = Z3_get_app_arg(ctx->z3_ctx, child_app, 1);
                Z3_ast iffalse = Z3_get_app_arg(ctx->z3_ctx, child_app, 2);

                // iftrue must be #b0 or #b1
                if (Z3_get_ast_kind(ctx->z3_ctx, iftrue) != Z3_NUMERAL_AST) {
                    res = 0;
                    break;
                }
                uint64_t iftrue_v;
                successGet = Z3_get_numeral_uint64(ctx->z3_ctx, iftrue,
                                                   (uint64_t*)&iftrue_v);
                if (!successGet || (iftrue_v != 0 && iftrue_v != 1)) {
                    res = 0;
                    break;
                }
                if (Z3_get_ast_kind(ctx->z3_ctx, iffalse) != Z3_NUMERAL_AST) {
                    res = 0;
                    break;
                }

                // iffalse must be #b0 or #b1
                uint64_t iffalse_v;
                successGet = Z3_get_numeral_uint64(ctx->z3_ctx, iftrue,
                                                   (uint64_t*)&iffalse_v);
                if (!successGet || (iffalse_v != 0 && iffalse_v != 1)) {
                    res = 0;
                    break;
                }

                // cond must be (= inp_i const_i)
                if (Z3_get_ast_kind(ctx->z3_ctx, cond) != Z3_APP_AST) {
                    res = 0;
                    break;
                }
                Z3_app       cond_app  = Z3_to_app(ctx->z3_ctx, cond);
                Z3_func_decl cond_decl = Z3_get_app_decl(ctx->z3_ctx, cond_app);
                Z3_decl_kind cond_decl_kind =
                    Z3_get_decl_kind(ctx->z3_ctx, cond_decl);
                if (cond_decl_kind != Z3_OP_EQ) {
                    res = 0;
                    break;
                }
                Z3_ast inp_i   = Z3_get_app_arg(ctx->z3_ctx, cond_app, 0);
                Z3_ast const_i = Z3_get_app_arg(ctx->z3_ctx, cond_app, 1);
                if (Z3_get_ast_kind(ctx->z3_ctx, inp_i) != Z3_APP_AST) {
                    res = 0;
                    break;
                }
                if (Z3_get_ast_kind(ctx->z3_ctx, const_i) != Z3_NUMERAL_AST) {
                    res = 0;
                    break;
                }
                Z3_app       inp_i_app = Z3_to_app(ctx->z3_ctx, inp_i);
                Z3_func_decl inp_i_decl =
                    Z3_get_app_decl(ctx->z3_ctx, inp_i_app);
                Z3_decl_kind inp_i_decl_kind =
                    Z3_get_decl_kind(ctx->z3_ctx, inp_i_decl);
                if (inp_i_decl_kind != Z3_OP_UNINTERPRETED) {
                    res = 0;
                    break;
                }
                int inp_i_idx = Z3_get_symbol_int(
                    ctx->z3_ctx, Z3_get_decl_name(ctx->z3_ctx, inp_i_decl));
                uint64_t const_i_v;
                successGet = Z3_get_numeral_uint64(ctx->z3_ctx, const_i,
                                                   (uint64_t*)&const_i_v);
                if (!successGet) {
                    res = 0;
                    break;
                }

                // finally. Set value
                values[inp_i_idx] = const_i_v;
                res               = 1;
            } else {
                res = 0;
                break;
            }
        }
        if (res)
            return res;
    }

    for (i = 0; i < num_fields; ++i) {
        res |= __detect_strcmp_pattern(ctx, Z3_get_app_arg(ctx->z3_ctx, app, i),
                                       values);
    }

    return res;
}

// *************************************************
// **************** HEURISTICS - END ***************
// *************************************************

static inline void __reset_ast_data()
{
    set_remove_all__digest_t(&ast_data.processed_set);
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

    opt_found = 0;

    __reset_ast_data();

    __detect_input_to_state_query(ctx, branch_condition, &ast_data);
    detect_involved_inputs_wrapper(ctx, branch_condition, &ast_data);
    __detect_early_constants(ctx, branch_condition, &ast_data);

    testcase_t* current_testcase = &ctx->testcases.data[0];
    memcpy(tmp_input, current_testcase->values,
           current_testcase->values_len * sizeof(unsigned long));
}

static inline unsigned char __extract_from_long(long value, unsigned int i)
{
    return (value >> i * 8) & 0xff;
}

static __always_inline int PHASE_reuse(fuzzy_ctx_t* ctx, Z3_ast query,
                                       Z3_ast                branch_condition,
                                       unsigned char const** proof,
                                       unsigned long*        proof_size)
{
    if (skip_reuse)
        return 0;

    assert(ctx->testcases.size > 1 && "PHASE_reuse not enough testcases");
#ifdef DEBUG_CHECK_LIGHT
    Z3FUZZ_LOG("Trying REUSE PHASE\n");
#endif
    unsigned i;
    for (i = 1; i < ctx->testcases.size; ++i) {
        testcase_t* testcase = &ctx->testcases.data[i];

        if (__evaluate_branch_query(ctx, query, branch_condition,
                                    testcase->values, testcase->value_sizes,
                                    testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - reuse] Query is SAT\n");
#endif
            __vals_long_to_char(testcase->values, tmp_proof,
                                testcase->testcase_len);
            ctx->stats.reuse++;
            *proof      = tmp_proof;
            *proof_size = testcase->testcase_len;
            return 1;
        }
    }
    return 0;
}

static __always_inline int PHASE_input_to_state(fuzzy_ctx_t* ctx, Z3_ast query,
                                                Z3_ast branch_condition,
                                                unsigned char const** proof,
                                                unsigned long* proof_size)
{
    if (unlikely(skip_input_to_state))
        return 0;

    assert(ast_data.is_input_to_state &&
           "PHASE_input_to_state not an input to state query");
#ifdef DEBUG_CHECK_LIGHT
    Z3FUZZ_LOG("Trying Input to State\n");
#endif
    testcase_t*    current_testcase = &ctx->testcases.data[0];
    index_group_t* group;
    unsigned int   index;
    unsigned char  b;
    unsigned       k;
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
    if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                current_testcase->value_sizes,
                                current_testcase->values_len)) {
#ifdef PRINT_SAT
        Z3FUZZ_LOG("[check light - input to state] Query is SAT\n");
#endif
        ctx->stats.input_to_state++;
        ctx->stats.num_sat++;
        __vals_long_to_char(tmp_input, tmp_proof,
                            current_testcase->testcase_len);
        *proof      = tmp_proof;
        *proof_size = current_testcase->testcase_len;
        return 1;
    }

    // if (ast_data.op_input_to_state == Z3_OP_EQ)
    //     // query is UNSAT
    //     return 2;

    // restore tmp_input
    for (k = 0; k < group->n; ++k) {
        index            = group->indexes[group->n - k - 1];
        tmp_input[index] = (unsigned long)current_testcase->values[index];
    }

    return 0;
}

static __always_inline int PHASE_input_to_state_extended(
    fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
    unsigned char const** proof, unsigned long* proof_size)
{
    if (unlikely(skip_input_to_state_extended))
        return 0;

    assert(ast_data.values.size > 0 &&
           "PHASE_input_to_state_extended  no early constants");

#ifdef DEBUG_CHECK_LIGHT
    Z3FUZZ_LOG("Trying Input to State Extended\n");
#endif
    testcase_t* current_testcase = &ctx->testcases.data[0];

    index_group_t* group;
    unsigned int   index;
    unsigned       i;
    unsigned       k;

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
            if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                        current_testcase->value_sizes,
                                        current_testcase->values_len)) {
#ifdef PRINT_SAT
                Z3FUZZ_LOG(
                    "[check light - input to state extended] Query is SAT\n");
#endif
                ctx->stats.input_to_state_ext++;
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
    return 0;
}

static __always_inline int PHASE_brute_force(fuzzy_ctx_t* ctx, Z3_ast query,
                                             Z3_ast branch_condition,
                                             unsigned char const** proof,
                                             unsigned long*        proof_size)
{
    if (unlikely(skip_brute_force))
        return 2;

    testcase_t*    current_testcase = &ctx->testcases.data[0];
    unsigned       i;
    unsigned long* uniq_index;

#ifdef DEBUG_CHECK_LIGHT
    Z3FUZZ_LOG("Trying Brute Force\n");
#endif

    uniq_index = NULL;
    set_reset_iter__ulong(&ast_data.indexes, 0);
    set_iter_next__ulong(&ast_data.indexes, 0, &uniq_index);

    for (i = 0; i < 256; ++i) {
        tmp_input[*uniq_index] = i;
        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - brute force] "
                       "Query is SAT\n");
#endif
            ctx->stats.brute_force++;
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
}

static __always_inline int
PHASE_gradient_descend(fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
                       unsigned char const** proof, unsigned long* proof_size)
{
    if (unlikely(skip_gradient_descend))
        return 0;

    testcase_t* current_testcase = &ctx->testcases.data[0];

#ifdef DEBUG_CHECK_LIGHT
    Z3FUZZ_LOG("Trying Gradient Descend\n");
#endif

    Z3_ast out_ast;
    int    valid_for_gd =
        __gradient_transf_init(ctx->z3_ctx, branch_condition, &out_ast);
    if (!valid_for_gd)
        return 0;

    eval_wapper_ctx_t ew;

    int valid_eval = __gd_init_eval(ctx, query, out_ast, 0, 0, &ew);
    assert(valid_eval == 1 && "eval should be always valid here");

    eval_set_ctx(&ew);
    set__digest_t digest_set;
    set_init__digest_t(&digest_set, digest_64bit_hash, digest_equals);

    uint64_t val;
    while (
        (gd_descend_transf(__gd_eval, ew.input, ew.input, &val,
                           ew.mapping_size) == 0) &&
        (__check_or_add_digest(&digest_set, (unsigned char*)ew.input,
                               ew.mapping_size * sizeof(unsigned long)) == 0)) {
        __gd_fix_tmp_input(ew.input);
        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - gradient descend] "
                       "Query is SAT\n");
#endif
            ctx->stats.gradient_descend++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            set_free__digest_t(&digest_set);
            __gd_free_eval(&ew);
            Z3_dec_ref(ctx->z3_ctx, out_ast);
            return 1;
        }
    }

    Z3_dec_ref(ctx->z3_ctx, out_ast);
    set_free__digest_t(&digest_set);
    __gd_restore_tmp_input(current_testcase);
    __gd_free_eval(&ew);
    return 0;
}

static __always_inline int SUBPHASE_afl_det_single_waliking_bit(
    fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
    unsigned char const** proof, unsigned long* proof_size,
    unsigned long input_index)
{
    if (unlikely(skip_afl_det_single_walking_bit))
        return 0;

    testcase_t*   current_testcase = &ctx->testcases.data[0];
    unsigned char input_byte_0 =
        (unsigned char)current_testcase->values[input_index];
    unsigned char tmp_byte;
    unsigned      i;

    // single walking bit
    for (i = 0; i < 8; ++i) {
        tmp_byte               = FLIP_BIT(input_byte_0, i);
        tmp_input[input_index] = (unsigned long)tmp_byte;
        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - flip1] "
                       "Query is SAT\n");
#endif
            ctx->stats.flip1++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
    }
    return 0;
}

static __always_inline int SUBPHASE_afl_det_two_waliking_bits(
    fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
    unsigned char const** proof, unsigned long* proof_size,
    unsigned long input_index)
{
    if (unlikely(skip_afl_det_two_walking_bit))
        return 0;

    testcase_t*   current_testcase = &ctx->testcases.data[0];
    unsigned char input_byte_0 =
        (unsigned char)current_testcase->values[input_index];
    unsigned char tmp_byte;
    unsigned      i;
    for (i = 0; i < 7; ++i) {
        tmp_byte               = FLIP_BIT(input_byte_0, i);
        tmp_byte               = FLIP_BIT(tmp_byte, i + 1);
        tmp_input[input_index] = (unsigned long)tmp_byte;
        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - flip2] "
                       "Query is SAT\n");
#endif
            ctx->stats.flip2++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
    }
    return 0;
}

static __always_inline int SUBPHASE_afl_det_four_waliking_bits(
    fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
    unsigned char const** proof, unsigned long* proof_size,
    unsigned long input_index)
{
    if (unlikely(skip_afl_det_four_walking_bit))
        return 0;

    testcase_t*   current_testcase = &ctx->testcases.data[0];
    unsigned char input_byte_0 =
        (unsigned char)current_testcase->values[input_index];
    unsigned char tmp_byte;
    unsigned      i;

    for (i = 0; i < 5; ++i) {
        tmp_byte               = FLIP_BIT(input_byte_0, i);
        tmp_byte               = FLIP_BIT(tmp_byte, i + 1);
        tmp_byte               = FLIP_BIT(tmp_byte, i + 2);
        tmp_byte               = FLIP_BIT(tmp_byte, i + 3);
        tmp_input[input_index] = (unsigned long)tmp_byte;
        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - flip4] "
                       "Query is SAT\n");
#endif
            ctx->stats.flip4++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
    }
    return 0;
}

static __always_inline int
SUBPHASE_afl_det_byte_flip(fuzzy_ctx_t* ctx, Z3_ast query,
                           Z3_ast branch_condition, unsigned char const** proof,
                           unsigned long* proof_size, unsigned long input_index)
{
    if (unlikely(skip_afl_det_byte_flip))
        return 0;

    testcase_t*   current_testcase = &ctx->testcases.data[0];
    unsigned char input_byte_0 =
        (unsigned char)current_testcase->values[input_index];

    tmp_input[input_index] = (unsigned long)input_byte_0 ^ 0xffUL;
    if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                current_testcase->value_sizes,
                                current_testcase->values_len)) {
#ifdef PRINT_SAT
        Z3FUZZ_LOG("[check light - flip8] "
                   "Query is SAT\n");
#endif
        ctx->stats.flip8++;
        ctx->stats.num_sat++;
        __vals_long_to_char(tmp_input, tmp_proof,
                            current_testcase->testcase_len);
        *proof      = tmp_proof;
        *proof_size = current_testcase->testcase_len;
        return 1;
    }
    return 0;
}

static __always_inline int
SUBPHASE_afl_det_arith8(fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
                        unsigned char const** proof, unsigned long* proof_size,
                        unsigned long input_index)
{
    if (unlikely(skip_afl_det_arith8))
        return 0;

    testcase_t*   current_testcase = &ctx->testcases.data[0];
    unsigned char input_byte_0 =
        (unsigned char)current_testcase->values[input_index];
    unsigned i;

    for (i = 1; i < 35; ++i) {
        tmp_input[input_index] = (unsigned char)(input_byte_0 + i);
        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - arith8-sum] "
                       "Query is SAT\n");
#endif
            ctx->stats.arith8_sum++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
        tmp_input[input_index] = (unsigned char)(input_byte_0 - i);
        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - arith8-sub] "
                       "Query is SAT\n");
#endif
            ctx->stats.arith8_sub++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
    }
    return 0;
}

static __always_inline int SUBPHASE_afl_det_int8(fuzzy_ctx_t* ctx, Z3_ast query,
                                                 Z3_ast branch_condition,
                                                 unsigned char const** proof,
                                                 unsigned long* proof_size,
                                                 unsigned long  input_index)
{
    if (unlikely(skip_afl_det_int8))
        return 0;

    testcase_t* current_testcase = &ctx->testcases.data[0];
    unsigned    i;

    for (i = 0; i < sizeof(interesting8); ++i) {
        tmp_input[input_index] = (unsigned char)(interesting8[i]);
        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - int8] "
                       "Query is SAT\n");
#endif
            ctx->stats.int8++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
    }
    return 0;
}

static __always_inline int SUBPHASE_afl_det_flip_short(
    fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
    unsigned char const** proof, unsigned long* proof_size,
    unsigned long input_index_0, unsigned long input_index_1)
{
    if (unlikely(skip_afl_det_flip_short))
        return 0;

    testcase_t*   current_testcase = &ctx->testcases.data[0];
    unsigned char input_byte_0 =
        (unsigned char)current_testcase->values[input_index_0];
    unsigned char input_byte_1 =
        (unsigned char)current_testcase->values[input_index_1];

    // flip short
    tmp_input[input_index_0] = (unsigned long)input_byte_0 ^ 0xffUL;
    tmp_input[input_index_1] = (unsigned long)input_byte_1 ^ 0xffUL;
    if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                current_testcase->value_sizes,
                                current_testcase->values_len)) {
#ifdef PRINT_SAT
        Z3FUZZ_LOG("[check light - flip16] "
                   "Query is SAT\n");
#endif
        ctx->stats.flip16++;
        ctx->stats.num_sat++;
        __vals_long_to_char(tmp_input, tmp_proof,
                            current_testcase->testcase_len);
        *proof      = tmp_proof;
        *proof_size = current_testcase->testcase_len;
        return 1;
    }
    return 0;
}

static __always_inline int
SUBPHASE_afl_det_arith16(fuzzy_ctx_t* ctx, Z3_ast query,
                         Z3_ast branch_condition, unsigned char const** proof,
                         unsigned long* proof_size, unsigned long input_index_0,
                         unsigned long input_index_1)
{
    if (unlikely(skip_afl_det_arith16))
        return 0;

    testcase_t*   current_testcase = &ctx->testcases.data[0];
    unsigned char input_byte_0 =
        (unsigned char)current_testcase->values[input_index_0];
    unsigned char input_byte_1 =
        (unsigned char)current_testcase->values[input_index_1];
    unsigned short input_word_LE = (input_byte_1 << 8) | input_byte_0;
    unsigned short input_word_BE = (input_byte_0 << 8) | input_byte_1;

    unsigned i;
    for (i = 1; i < 35; ++i) {
        tmp_input[input_index_0] = (unsigned long)(input_word_LE + i) & 0xffUL;
        tmp_input[input_index_1] =
            (unsigned long)((input_word_LE + i) >> 8) & 0xffUL;

        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - arith16-sum-LE] "
                       "Query is SAT\n");
#endif
            ctx->stats.arith16_sum_LE++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
        tmp_input[input_index_0] = (unsigned long)(input_word_LE - i) & 0xffUL;
        tmp_input[input_index_1] =
            (unsigned long)((input_word_LE - i) >> 8) & 0xffUL;

        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - arith16-sub-LE] "
                       "Query is SAT\n");
#endif
            ctx->stats.arith16_sub_LE++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
        tmp_input[input_index_0] = (unsigned long)(input_word_BE + i) & 0xffUL;
        tmp_input[input_index_1] =
            (unsigned long)((input_word_BE + i) >> 8) & 0xffUL;

        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - arith16-sum-BE] "
                       "Query is SAT\n");
#endif
            ctx->stats.arith16_sum_BE++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
        tmp_input[input_index_0] = (unsigned long)(input_word_BE - i) & 0xffUL;
        tmp_input[input_index_1] =
            (unsigned long)((input_word_BE - i) >> 8) & 0xffUL;

        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - arith16-sub-BE] "
                       "Query is SAT\n");
#endif
            ctx->stats.arith32_sub_BE++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
    }
    return 0;
}

static __always_inline int
SUBPHASE_afl_det_int16(fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
                       unsigned char const** proof, unsigned long* proof_size,
                       unsigned long input_index_0, unsigned long input_index_1)
{
    if (unlikely(skip_afl_det_int16))
        return 0;
    testcase_t* current_testcase = &ctx->testcases.data[0];

    unsigned i;
    for (i = 0; i < sizeof(interesting16) / sizeof(short); ++i) {
        tmp_input[input_index_0] = (unsigned long)(interesting16[i]) & 0xffUL;
        tmp_input[input_index_1] =
            (unsigned long)(interesting16[i] >> 8) & 0xffUL;

        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - int16] "
                       "Query is SAT\n");
#endif
            ctx->stats.int16++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
    }
    return 0;
}

static __always_inline int SUBPHASE_afl_det_flip_int(
    fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
    unsigned char const** proof, unsigned long* proof_size,
    unsigned long input_index_0, unsigned long input_index_1,
    unsigned long input_index_2, unsigned long input_index_3)
{
    if (unlikely(skip_afl_det_flip_int))
        return 0;

    testcase_t* current_testcase = &ctx->testcases.data[0];

    unsigned char input_byte_0 =
        (unsigned char)current_testcase->values[input_index_0];
    unsigned char input_byte_1 =
        (unsigned char)current_testcase->values[input_index_1];
    unsigned char input_byte_2 =
        (unsigned char)current_testcase->values[input_index_2];
    unsigned char input_byte_3 =
        (unsigned char)current_testcase->values[input_index_3];

    tmp_input[input_index_0] = (unsigned long)input_byte_0 ^ 0xffUL;
    tmp_input[input_index_1] = (unsigned long)input_byte_1 ^ 0xffUL;
    tmp_input[input_index_2] = (unsigned long)input_byte_2 ^ 0xffUL;
    tmp_input[input_index_3] = (unsigned long)input_byte_3 ^ 0xffUL;

    if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                current_testcase->value_sizes,
                                current_testcase->values_len)) {
#ifdef PRINT_SAT
        Z3FUZZ_LOG("[check light - flip32] "
                   "Query is SAT\n");
#endif
        ctx->stats.flip32++;
        ctx->stats.num_sat++;
        __vals_long_to_char(tmp_input, tmp_proof,
                            current_testcase->testcase_len);
        *proof      = tmp_proof;
        *proof_size = current_testcase->testcase_len;
        return 1;
    }
    return 0;
}

static __always_inline int SUBPHASE_afl_det_arith32(
    fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
    unsigned char const** proof, unsigned long* proof_size,
    unsigned long input_index_0, unsigned long input_index_1,
    unsigned long input_index_2, unsigned long input_index_3)
{
    if (unlikely(skip_afl_det_arith32))
        return 0;

    testcase_t* current_testcase = &ctx->testcases.data[0];

    unsigned char input_byte_0 =
        (unsigned char)current_testcase->values[input_index_0];
    unsigned char input_byte_1 =
        (unsigned char)current_testcase->values[input_index_1];
    unsigned char input_byte_2 =
        (unsigned char)current_testcase->values[input_index_2];
    unsigned char input_byte_3 =
        (unsigned char)current_testcase->values[input_index_3];
    unsigned input_dword_LE = (input_byte_3 << 24) | (input_byte_2 << 16) |
                              (input_byte_1 << 8) | input_byte_0;
    unsigned input_dword_BE = (input_byte_0 << 24) | (input_byte_1 << 16) |
                              (input_byte_2 << 8) | input_byte_3;

    unsigned i;
    for (i = 1; i < 35; ++i) {
        tmp_input[input_index_0] = (unsigned long)(input_dword_LE + i) & 0xffUL;
        tmp_input[input_index_1] =
            (unsigned long)((input_dword_LE + i) >> 8) & 0xffUL;
        tmp_input[input_index_2] =
            (unsigned long)((input_dword_LE + i) >> 16) & 0xffUL;
        tmp_input[input_index_3] =
            (unsigned long)((input_dword_LE + i) >> 24) & 0xffUL;

        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - arith32-sum-LE] "
                       "Query is SAT\n");
#endif
            ctx->stats.arith32_sum_LE++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
        tmp_input[input_index_0] = (unsigned long)(input_dword_LE - i) & 0xffUL;
        tmp_input[input_index_1] =
            (unsigned long)((input_dword_LE - i) >> 8) & 0xffUL;
        tmp_input[input_index_2] =
            (unsigned long)((input_dword_LE - i) >> 16) & 0xffUL;
        tmp_input[input_index_3] =
            (unsigned long)((input_dword_LE - i) >> 24) & 0xffUL;

        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - arith32-sub-LE] "
                       "Query is SAT\n");
#endif
            ctx->stats.arith32_sub_LE++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
        tmp_input[input_index_0] = (unsigned long)(input_dword_BE + i) & 0xffUL;
        tmp_input[input_index_1] =
            (unsigned long)((input_dword_BE + i) >> 8) & 0xffUL;
        tmp_input[input_index_2] =
            (unsigned long)((input_dword_BE + i) >> 16) & 0xffUL;
        tmp_input[input_index_3] =
            (unsigned long)((input_dword_BE + i) >> 24) & 0xffUL;

        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - arith32-sum-BE] "
                       "Query is SAT\n");
#endif
            ctx->stats.arith32_sum_BE++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
        tmp_input[input_index_0] = (unsigned long)(input_dword_BE - i) & 0xffU;
        tmp_input[input_index_1] =
            (unsigned long)((input_dword_BE - i) >> 8) & 0xffU;
        tmp_input[input_index_2] =
            (unsigned long)((input_dword_BE - i) >> 16) & 0xffU;
        tmp_input[input_index_3] =
            (unsigned long)((input_dword_BE - i) >> 24) & 0xffU;

        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - arith32-sub-BE] "
                       "Query is SAT\n");
#endif
            ctx->stats.arith32_sub_BE++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
    }
    return 0;
}

static __always_inline int
SUBPHASE_afl_det_int32(fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
                       unsigned char const** proof, unsigned long* proof_size,
                       unsigned long input_index_0, unsigned long input_index_1,
                       unsigned long input_index_2, unsigned long input_index_3)
{
    if (unlikely(skip_afl_det_int32))
        return 0;

    testcase_t* current_testcase = &ctx->testcases.data[0];

    unsigned i;
    for (i = 0; i < sizeof(interesting32) / sizeof(int); ++i) {
        tmp_input[input_index_0] = (unsigned long)(interesting32[i]) & 0xffU;
        tmp_input[input_index_1] =
            (unsigned long)(interesting32[i] >> 8) & 0xffU;
        tmp_input[input_index_2] =
            (unsigned long)(interesting32[i] >> 16) & 0xffU;
        tmp_input[input_index_3] =
            (unsigned long)(interesting32[i] >> 24) & 0xffU;

        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - int32] "
                       "Query is SAT\n");
#endif
            ctx->stats.int32++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
    }
    return 0;
}

static __always_inline int SUBPHASE_afl_det_flip_long(
    fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
    unsigned char const** proof, unsigned long* proof_size,
    unsigned long input_index_0, unsigned long input_index_1,
    unsigned long input_index_2, unsigned long input_index_3,
    unsigned long input_index_4, unsigned long input_index_5,
    unsigned long input_index_6, unsigned long input_index_7)
{
    if (unlikely(skip_afl_det_flip_long))
        return 0;

    testcase_t* current_testcase = &ctx->testcases.data[0];

    unsigned char input_byte_0 =
        (unsigned char)current_testcase->values[input_index_0];
    unsigned char input_byte_1 =
        (unsigned char)current_testcase->values[input_index_1];
    unsigned char input_byte_2 =
        (unsigned char)current_testcase->values[input_index_2];
    unsigned char input_byte_3 =
        (unsigned char)current_testcase->values[input_index_3];
    unsigned char input_byte_4 =
        (unsigned char)current_testcase->values[input_index_4];
    unsigned char input_byte_5 =
        (unsigned char)current_testcase->values[input_index_5];
    unsigned char input_byte_6 =
        (unsigned char)current_testcase->values[input_index_6];
    unsigned char input_byte_7 =
        (unsigned char)current_testcase->values[input_index_7];

    tmp_input[input_index_0] = (unsigned long)input_byte_0 ^ 0xffUL;
    tmp_input[input_index_1] = (unsigned long)input_byte_1 ^ 0xffUL;
    tmp_input[input_index_2] = (unsigned long)input_byte_2 ^ 0xffUL;
    tmp_input[input_index_3] = (unsigned long)input_byte_3 ^ 0xffUL;
    tmp_input[input_index_4] = (unsigned long)input_byte_4 ^ 0xffUL;
    tmp_input[input_index_5] = (unsigned long)input_byte_5 ^ 0xffUL;
    tmp_input[input_index_6] = (unsigned long)input_byte_6 ^ 0xffUL;
    tmp_input[input_index_7] = (unsigned long)input_byte_7 ^ 0xffUL;

    if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                current_testcase->value_sizes,
                                current_testcase->values_len)) {
#ifdef PRINT_SAT
        Z3FUZZ_LOG("[check light - flip64] "
                   "Query is SAT\n");
#endif
        ctx->stats.flip64++;
        ctx->stats.num_sat++;
        __vals_long_to_char(tmp_input, tmp_proof,
                            current_testcase->testcase_len);
        *proof      = tmp_proof;
        *proof_size = current_testcase->testcase_len;
        return 1;
    }
    return 0;
}

static __always_inline int SUBPHASE_afl_det_arith64(
    fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
    unsigned char const** proof, unsigned long* proof_size,
    unsigned long input_index_0, unsigned long input_index_1,
    unsigned long input_index_2, unsigned long input_index_3,
    unsigned long input_index_4, unsigned long input_index_5,
    unsigned long input_index_6, unsigned long input_index_7)
{
    if (unlikely(skip_afl_det_arith64))
        return 0;

    testcase_t* current_testcase = &ctx->testcases.data[0];

    unsigned char input_byte_0 =
        (unsigned char)current_testcase->values[input_index_0];
    unsigned char input_byte_1 =
        (unsigned char)current_testcase->values[input_index_1];
    unsigned char input_byte_2 =
        (unsigned char)current_testcase->values[input_index_2];
    unsigned char input_byte_3 =
        (unsigned char)current_testcase->values[input_index_3];
    unsigned char input_byte_4 =
        (unsigned char)current_testcase->values[input_index_4];
    unsigned char input_byte_5 =
        (unsigned char)current_testcase->values[input_index_5];
    unsigned char input_byte_6 =
        (unsigned char)current_testcase->values[input_index_6];
    unsigned char input_byte_7 =
        (unsigned char)current_testcase->values[input_index_7];

    unsigned long input_qword_LE =
        ((ulong)input_byte_7 << 56) | ((ulong)input_byte_6 << 48) |
        ((ulong)input_byte_5 << 40) | ((ulong)input_byte_4 << 32) |
        ((ulong)input_byte_3 << 24) | ((ulong)input_byte_2 << 16) |
        ((ulong)input_byte_1 << 8) | (ulong)input_byte_0;
    unsigned long input_qword_BE =
        ((ulong)input_byte_0 << 56) | ((ulong)input_byte_1 << 48) |
        ((ulong)input_byte_2 << 40) | ((ulong)input_byte_3 << 32) |
        ((ulong)input_byte_4 << 24) | ((ulong)input_byte_5 << 16) |
        ((ulong)input_byte_6 << 8) | (ulong)input_byte_7;

    unsigned i;
    for (i = 1; i < 35; ++i) {
        tmp_input[input_index_0] = (unsigned long)(input_qword_LE + i) & 0xffUL;
        tmp_input[input_index_1] =
            (unsigned long)((input_qword_LE + i) >> 8) & 0xffUL;
        tmp_input[input_index_2] =
            (unsigned long)((input_qword_LE + i) >> 16) & 0xffUL;
        tmp_input[input_index_3] =
            (unsigned long)((input_qword_LE + i) >> 24) & 0xffUL;
        tmp_input[input_index_4] =
            (unsigned long)((input_qword_LE + i) >> 32) & 0xffUL;
        tmp_input[input_index_5] =
            (unsigned long)((input_qword_LE + i) >> 40) & 0xffUL;
        tmp_input[input_index_6] =
            (unsigned long)((input_qword_LE + i) >> 48) & 0xffUL;
        tmp_input[input_index_7] =
            (unsigned long)((input_qword_LE + i) >> 56) & 0xffUL;

        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - arith64-sum-LE] "
                       "Query is SAT\n");
#endif
            ctx->stats.arith64_sum_LE++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
        tmp_input[input_index_0] = (unsigned long)(input_qword_LE + i) & 0xffUL;
        tmp_input[input_index_1] =
            (unsigned long)((input_qword_LE + i) >> 8) & 0xffUL;
        tmp_input[input_index_2] =
            (unsigned long)((input_qword_LE + i) >> 16) & 0xffUL;
        tmp_input[input_index_3] =
            (unsigned long)((input_qword_LE + i) >> 24) & 0xffUL;
        tmp_input[input_index_4] =
            (unsigned long)((input_qword_LE + i) >> 32) & 0xffUL;
        tmp_input[input_index_5] =
            (unsigned long)((input_qword_LE + i) >> 40) & 0xffUL;
        tmp_input[input_index_6] =
            (unsigned long)((input_qword_LE + i) >> 48) & 0xffUL;
        tmp_input[input_index_7] =
            (unsigned long)((input_qword_LE + i) >> 56) & 0xffUL;
        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - arith64-sub-LE] "
                       "Query is SAT\n");
#endif
            ctx->stats.arith64_sub_LE++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
        tmp_input[input_index_0] = (unsigned long)(input_qword_BE + i) & 0xffUL;
        tmp_input[input_index_1] =
            (unsigned long)((input_qword_BE + i) >> 8) & 0xffUL;
        tmp_input[input_index_2] =
            (unsigned long)((input_qword_BE + i) >> 16) & 0xffUL;
        tmp_input[input_index_3] =
            (unsigned long)((input_qword_BE + i) >> 24) & 0xffUL;
        tmp_input[input_index_4] =
            (unsigned long)((input_qword_BE + i) >> 32) & 0xffUL;
        tmp_input[input_index_5] =
            (unsigned long)((input_qword_BE + i) >> 40) & 0xffUL;
        tmp_input[input_index_6] =
            (unsigned long)((input_qword_BE + i) >> 48) & 0xffUL;
        tmp_input[input_index_7] =
            (unsigned long)((input_qword_BE + i) >> 56) & 0xffUL;

        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - arith64-sum-BE] "
                       "Query is SAT\n");
#endif
            ctx->stats.arith64_sum_BE++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
        tmp_input[input_index_0] = (unsigned long)(input_qword_BE + i) & 0xffUL;
        tmp_input[input_index_1] =
            (unsigned long)((input_qword_BE + i) >> 8) & 0xffUL;
        tmp_input[input_index_2] =
            (unsigned long)((input_qword_BE + i) >> 16) & 0xffUL;
        tmp_input[input_index_3] =
            (unsigned long)((input_qword_BE + i) >> 24) & 0xffUL;
        tmp_input[input_index_4] =
            (unsigned long)((input_qword_BE + i) >> 32) & 0xffUL;
        tmp_input[input_index_5] =
            (unsigned long)((input_qword_BE + i) >> 40) & 0xffUL;
        tmp_input[input_index_6] =
            (unsigned long)((input_qword_BE + i) >> 48) & 0xffUL;
        tmp_input[input_index_7] =
            (unsigned long)((input_qword_BE + i) >> 56) & 0xffUL;

        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - arith64-sub-BE] "
                       "Query is SAT\n");
#endif
            ctx->stats.arith64_sub_BE++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
    }
    return 0;
}

static __always_inline int
SUBPHASE_afl_det_int64(fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
                       unsigned char const** proof, unsigned long* proof_size,
                       unsigned long input_index_0, unsigned long input_index_1,
                       unsigned long input_index_2, unsigned long input_index_3,
                       unsigned long input_index_4, unsigned long input_index_5,
                       unsigned long input_index_6, unsigned long input_index_7)
{
    if (unlikely(skip_afl_det_int32))
        return 0;

    testcase_t* current_testcase = &ctx->testcases.data[0];

    unsigned i;
    for (i = 0; i < sizeof(interesting64) / sizeof(long); ++i) {
        tmp_input[input_index_0] = (unsigned long)(interesting64[i]) & 0xffU;
        tmp_input[input_index_1] =
            (unsigned long)(interesting64[i] >> 8) & 0xffU;
        tmp_input[input_index_2] =
            (unsigned long)(interesting64[i] >> 16) & 0xffU;
        tmp_input[input_index_3] =
            (unsigned long)(interesting64[i] >> 24) & 0xffU;
        tmp_input[input_index_4] =
            (unsigned long)(interesting64[i] >> 24) & 0xffU;
        tmp_input[input_index_5] =
            (unsigned long)(interesting64[i] >> 24) & 0xffU;
        tmp_input[input_index_6] =
            (unsigned long)(interesting64[i] >> 24) & 0xffU;
        tmp_input[input_index_7] =
            (unsigned long)(interesting64[i] >> 24) & 0xffU;

        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[check light - int64] "
                       "Query is SAT\n");
#endif
            ctx->stats.int64++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
    }
    return 0;
}

static __always_inline int PHASE_afl_deterministic_groups(
    fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
    unsigned char const** proof, unsigned long* proof_size)
{
    if (unlikely(skip_afl_deterministic))
        return 0;

    int            ret;
    testcase_t*    current_testcase = &ctx->testcases.data[0];
    index_group_t* g;

#ifdef DEBUG_CHECK_LIGHT
    Z3FUZZ_LOG("Trying AFL Deterministic (groups)\n");
#endif

    set_reset_iter__index_group_t(&ast_data.index_groups, 1);
    while (set_iter_next__index_group_t(&ast_data.index_groups, 1, &g)) {
        unsigned i;
        // flip 1/2/4 int8 -> do for every group type
        for (i = 0; i < g->n; ++i) {
            unsigned long input_index = g->indexes[i];

            ret = SUBPHASE_afl_det_single_waliking_bit(
                ctx, query, branch_condition, proof, proof_size, input_index);
            if (ret)
                return 1;

            ret = SUBPHASE_afl_det_two_waliking_bits(
                ctx, query, branch_condition, proof, proof_size, input_index);
            if (ret)
                return 1;

            ret = SUBPHASE_afl_det_four_waliking_bits(
                ctx, query, branch_condition, proof, proof_size, input_index);
            if (ret)
                return 1;

            ret = SUBPHASE_afl_det_int8(ctx, query, branch_condition, proof,
                                        proof_size, input_index);
            if (ret)
                return 1;

            tmp_input[input_index] =
                (unsigned long)current_testcase->values[input_index];
        }

        switch (g->n) {
            case 2: {
                // flip short
                ret = SUBPHASE_afl_det_flip_short(ctx, query, branch_condition,
                                                  proof, proof_size,
                                                  g->indexes[0], g->indexes[1]);
                if (ret)
                    return 1;

                // 16-bit arithmetics
                ret = SUBPHASE_afl_det_arith16(ctx, query, branch_condition,
                                               proof, proof_size, g->indexes[0],
                                               g->indexes[1]);
                if (ret)
                    return 1;

                // interesting 16
                ret = SUBPHASE_afl_det_int16(ctx, query, branch_condition,
                                             proof, proof_size, g->indexes[0],
                                             g->indexes[1]);
                if (ret)
                    return 1;

                tmp_input[g->indexes[0]] =
                    current_testcase->values[g->indexes[0]];
                tmp_input[g->indexes[1]] =
                    current_testcase->values[g->indexes[1]];
                break;
            }
            case 4: {
                // flip int
                ret = SUBPHASE_afl_det_flip_int(
                    ctx, query, branch_condition, proof, proof_size,
                    g->indexes[0], g->indexes[1], g->indexes[2], g->indexes[3]);
                if (ret)
                    return 1;

                // 32-bit arithmetics
                ret = SUBPHASE_afl_det_arith32(
                    ctx, query, branch_condition, proof, proof_size,
                    g->indexes[0], g->indexes[1], g->indexes[2], g->indexes[3]);
                if (ret)
                    return 1;

                // interesting 32
                ret = SUBPHASE_afl_det_int32(
                    ctx, query, branch_condition, proof, proof_size,
                    g->indexes[0], g->indexes[1], g->indexes[2], g->indexes[3]);
                if (ret)
                    return 1;

                tmp_input[g->indexes[0]] =
                    current_testcase->values[g->indexes[0]];
                tmp_input[g->indexes[1]] =
                    current_testcase->values[g->indexes[1]];
                tmp_input[g->indexes[2]] =
                    current_testcase->values[g->indexes[2]];
                tmp_input[g->indexes[3]] =
                    current_testcase->values[g->indexes[3]];

                break;
            }
            case 8: {
                // flip long
                ret = SUBPHASE_afl_det_flip_long(
                    ctx, query, branch_condition, proof, proof_size,
                    g->indexes[0], g->indexes[1], g->indexes[2], g->indexes[3],
                    g->indexes[4], g->indexes[5], g->indexes[6], g->indexes[7]);
                if (ret)
                    return 1;

                // 64-bit arithmetics
                ret = SUBPHASE_afl_det_arith64(
                    ctx, query, branch_condition, proof, proof_size,
                    g->indexes[0], g->indexes[1], g->indexes[2], g->indexes[3],
                    g->indexes[4], g->indexes[5], g->indexes[6], g->indexes[7]);
                if (ret)
                    return 1;

                // interesting 64
                ret = SUBPHASE_afl_det_int64(
                    ctx, query, branch_condition, proof, proof_size,
                    g->indexes[0], g->indexes[1], g->indexes[2], g->indexes[3],
                    g->indexes[4], g->indexes[5], g->indexes[6], g->indexes[7]);
                if (ret)
                    return 1;

                tmp_input[g->indexes[0]] =
                    current_testcase->values[g->indexes[0]];
                tmp_input[g->indexes[1]] =
                    current_testcase->values[g->indexes[1]];
                tmp_input[g->indexes[2]] =
                    current_testcase->values[g->indexes[2]];
                tmp_input[g->indexes[3]] =
                    current_testcase->values[g->indexes[3]];
                tmp_input[g->indexes[4]] =
                    current_testcase->values[g->indexes[4]];
                tmp_input[g->indexes[5]] =
                    current_testcase->values[g->indexes[5]];
                tmp_input[g->indexes[6]] =
                    current_testcase->values[g->indexes[6]];
                tmp_input[g->indexes[7]] =
                    current_testcase->values[g->indexes[7]];
                break;
            }
            default: {
                // group size 1 and group with strange sizes (e.g. 3, probably
                // errors in the detection method)
                unsigned i;
                for (i = 0; i < g->n; ++i) {
                    // byte flip
                    ret = SUBPHASE_afl_det_byte_flip(ctx, query,
                                                     branch_condition, proof,
                                                     proof_size, g->indexes[i]);
                    if (ret)
                        return 1;

                    // 8-bit arithmetics
                    ret = SUBPHASE_afl_det_arith8(ctx, query, branch_condition,
                                                  proof, proof_size,
                                                  g->indexes[i]);
                    if (ret)
                        return 1;

                    tmp_input[g->indexes[0]] =
                        (unsigned long)current_testcase->values[g->indexes[i]];
                }
                break;
            }
        }
    }
    return 0;
}

static __always_inline int
PHASE_afl_deterministic(fuzzy_ctx_t* ctx, Z3_ast query, Z3_ast branch_condition,
                        unsigned char const** proof, unsigned long* proof_size)
{

    if (unlikely(skip_afl_deterministic))
        return 0;

    testcase_t* current_testcase = &ctx->testcases.data[0];

#ifdef DEBUG_CHECK_LIGHT
    Z3FUZZ_LOG("Trying AFL Deterministic\n");
#endif
    ulong*        p;
    unsigned long input_index_0, input_index_1, input_index_2, input_index_3;
    int           ret;

    set_reset_iter__ulong(&ast_data.indexes, 1);
    while (set_iter_next__ulong(&ast_data.indexes, 1, &p)) {
        input_index_0 = *p;
        // ****************
        // ***** byte *****
        // ****************

        // single waling bit
        ret = SUBPHASE_afl_det_single_waliking_bit(
            ctx, query, branch_condition, proof, proof_size, input_index_0);
        if (ret)
            return 1;

        // two walking bits
        ret = SUBPHASE_afl_det_two_waliking_bits(
            ctx, query, branch_condition, proof, proof_size, input_index_0);
        if (ret)
            return 1;

        // four walking bits
        ret = SUBPHASE_afl_det_four_waliking_bits(
            ctx, query, branch_condition, proof, proof_size, input_index_0);
        if (ret)
            return 1;

        // byte flip
        ret = SUBPHASE_afl_det_byte_flip(ctx, query, branch_condition, proof,
                                         proof_size, input_index_0);
        if (ret)
            return 1;

        // 8-bit arithmetics
        ret = SUBPHASE_afl_det_arith8(ctx, query, branch_condition, proof,
                                      proof_size, input_index_0);
        if (ret)
            return 1;

        // interesting 8
        ret = SUBPHASE_afl_det_int8(ctx, query, branch_condition, proof,
                                    proof_size, input_index_0);
        if (ret)
            return 1;

        tmp_input[input_index_0] =
            (unsigned long)current_testcase->values[input_index_0];
        if (!set_check__ulong(&ast_data.indexes, input_index_0 + 1))
            continue; // only one byte. Skip

        // ****************
        // ***** word *****
        // ****************
        input_index_1 = input_index_0 + 1;

        // flip short
        ret = SUBPHASE_afl_det_flip_short(ctx, query, branch_condition, proof,
                                          proof_size, input_index_0,
                                          input_index_1);
        if (ret)
            return 1;

        // 16-bit arithmetics
        ret =
            SUBPHASE_afl_det_arith16(ctx, query, branch_condition, proof,
                                     proof_size, input_index_0, input_index_1);
        if (ret)
            return 1;

        // interesting 16
        ret = SUBPHASE_afl_det_int16(ctx, query, branch_condition, proof,
                                     proof_size, input_index_0, input_index_1);
        if (ret)
            return 1;

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

        // flip int
        ret = SUBPHASE_afl_det_flip_int(
            ctx, query, branch_condition, proof, proof_size, input_index_0,
            input_index_1, input_index_2, input_index_3);
        if (ret)
            return 1;

        // 32-bit arithmetics
        ret = SUBPHASE_afl_det_arith32(ctx, query, branch_condition, proof,
                                       proof_size, input_index_0, input_index_1,
                                       input_index_2, input_index_3);
        if (ret)
            return 1;

        // interesting 32
        ret = SUBPHASE_afl_det_int32(ctx, query, branch_condition, proof,
                                     proof_size, input_index_0, input_index_1,
                                     input_index_2, input_index_3);
        if (ret)
            return 1;

        tmp_input[input_index_0] = current_testcase->values[input_index_0];
        tmp_input[input_index_1] = current_testcase->values[input_index_1];
        tmp_input[input_index_2] = current_testcase->values[input_index_2];
        tmp_input[input_index_3] = current_testcase->values[input_index_3];
    }

    return 0;
}

static __always_inline int PHASE_afl_havoc(fuzzy_ctx_t* ctx, Z3_ast query,
                                           Z3_ast branch_condition,
                                           unsigned char const** proof,
                                           unsigned long*        proof_size)
{

    if (skip_afl_havoc)
        return 0;

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
    testcase_t*     current_testcase = &ctx->testcases.data[0];
    index_group_t*  group;

    unsigned i;
    ulong*   p;

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
                tmp_input[index_0] = val & 0xff;
                tmp_input[index_1] = (val >> 8) & 0xff;
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
        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
#ifdef PRINT_SAT
            Z3FUZZ_LOG("[havoc L5] "
                       "Query is SAT\n");
#endif
            ctx->stats.havoc++;
            ctx->stats.num_sat++;
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            havoc_res   = 1;
        }
    }

    free(indexes);
    free(ig_16);
    free(ig_32);
    free(ig_64);
    return havoc_res;
}

static int __query_check_light(fuzzy_ctx_t* ctx, Z3_ast query,
                               Z3_ast                branch_condition,
                               unsigned char const** proof,
                               unsigned long*        proof_size)
{
    // 1 -> succeded
#ifdef DEBUG_CHECK_LIGHT
    Z3FUZZ_LOG("query: \n%s\n", Z3_ast_to_string(ctx->z3_ctx, query));
    Z3FUZZ_LOG("branch condition: \n%s\n\n",
               Z3_ast_to_string(ctx->z3_ctx, branch_condition));
#endif
    testcase_t* current_testcase = &ctx->testcases.data[0];
    int         res;

    // L0 -- REUSE PHASE
    if (ctx->testcases.size > 1) {
        res = PHASE_reuse(ctx, query, branch_condition, proof, proof_size);
        if (res)
            return 1;
    }

    // common code, this must be executed for the subsequent levels to work
    __init_global_data(ctx, query, branch_condition);
    if (log_query_stats)
        fprintf(query_log, "\n%lu;%lu;%lu;%s;%u;%u", ast_data.query_size,
                ast_data.indexes.size, ast_data.index_groups.size,
                ast_data.is_input_to_state ? "true" : "false",
                ast_data.linear_arithmetic_operations,
                ast_data.nonlinear_arithmetic_operations);
    if (ast_data.indexes.size == 0) { // constant branch condition!
        if (__evaluate_branch_query(ctx, query, branch_condition, tmp_input,
                                    current_testcase->value_sizes,
                                    current_testcase->values_len)) {
            __vals_long_to_char(tmp_input, tmp_proof,
                                current_testcase->testcase_len);
            *proof      = tmp_proof;
            *proof_size = current_testcase->testcase_len;
            return 1;
        }
        return 0;
    }

#ifdef DEBUG_CHECK_LIGHT
    print_index_and_value_queue(&ast_data);
#endif
    // Input to State
    if (ast_data.is_input_to_state) {
        // input to state detected
        res = PHASE_input_to_state(ctx, query, branch_condition, proof,
                                   proof_size);
        if (res == 2)
            return 0;
        if (res == 1)
            return 1;
    }

    // Input to State Extended
    if (ast_data.values.size > 0) {
        int res = PHASE_input_to_state_extended(ctx, query, branch_condition,
                                                proof, proof_size);
        if (res)
            return 1;
    }

    // Pure Brute Force - Only One Byte is Involved
    if (ast_data.indexes.size == 1) {
        // if the fase fails, we exit -> the query is UNSAT
        res =
            PHASE_brute_force(ctx, query, branch_condition, proof, proof_size);
        if (res != 2)
            return res;
    }

    // Gradient Based Transformation
    res =
        PHASE_gradient_descend(ctx, query, branch_condition, proof, proof_size);
    if (res)
        return 1;

        // Afl Deterministic Transformations
#ifdef USE_AFL_DET_GROUPS
    res = PHASE_afl_deterministic_groups(ctx, query, branch_condition, proof,
                                         proof_size);
#else
    res = PHASE_afl_deterministic(ctx, query, branch_condition, proof,
                                  proof_size);
#endif
    if (res)
        return 1;

    // Afl Havoc Transformation
    res = PHASE_afl_havoc(ctx, query, branch_condition, proof, proof_size);
    if (res)
        return 1;

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
               "z3fuzz_add_assignment() ctx->assignments - failed realloc");

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

        if (testcase->values_len <= idx) {
            testcase->values_len = (idx + 1) * 3 / 2;
            testcase->values     = (unsigned long*)realloc(
                testcase->values, sizeof(unsigned long) * testcase->values_len);
            assert(testcase->values != 0 &&
                   "z3fuzz_add_assignment() testcase->values - failed realloc");
            testcase->value_sizes = (unsigned char*)realloc(
                testcase->value_sizes,
                sizeof(unsigned char) * testcase->values_len);
            assert(testcase->value_sizes != 0 &&
                   "z3fuzz_add_assignment() testcase->value_sizes - failed "
                   "realloc");
            testcase->z3_values = (Z3_ast*)realloc(
                testcase->z3_values, sizeof(Z3_ast) * testcase->values_len);
            assert(
                testcase->z3_values != 0 &&
                "z3fuzz_add_assignment() testcase->z3_values - failed realloc");
            memset(testcase->z3_values + old_len, 0,
                   testcase->values_len - old_len);
        }

        unsigned long assignment_value_concrete =
            ctx->model_eval(ctx->z3_ctx, assignment_value, testcase->values,
                            testcase->value_sizes, testcase->values_len);

        testcase->value_sizes[idx] = assignment_size;
        testcase->values[idx]      = assignment_value_concrete;
        testcase->z3_values[idx] =
            Z3_mk_unsigned_int(ctx->z3_ctx, assignment_value_concrete,
                               Z3_mk_bv_sort(ctx->z3_ctx, assignment_size));
        Z3_inc_ref(ctx->z3_ctx, testcase->z3_values[idx]);

        testcase->values_len =
            (testcase->values_len > idx + 1) ? testcase->values_len : idx + 1;
    }

    if (old_len < ctx->testcases.data[0].values_len) {
        tmp_input = (unsigned long*)realloc(
            tmp_input,
            sizeof(unsigned long) * ctx->testcases.data[0].values_len);
        assert(tmp_input != 0 &&
               "z3fuzz_add_assignment() tmp_input - failed realloc");
    }
}

static int compare_ulong(const void* v1, const void* v2)
{
    return *(unsigned long*)v1 - *(unsigned long*)v2;
}

static inline unsigned long __minimize_maximize_inner_greedy(
    fuzzy_ctx_t* ctx, Z3_ast pi, Z3_ast to_maximize_minimize,
    unsigned char const** out_values, unsigned is_max)
{
    __reset_ast_data();
    detect_involved_inputs_wrapper(ctx, to_maximize_minimize, &ast_data);

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
    memcpy(tmp_input, ctx->testcases.data[0].values,
           ctx->testcases.data[0].values_len * sizeof(unsigned long));

    *out_len = ctx->testcases.data[0].testcase_len;
    if (use_greedy_mamin)
        return __minimize_maximize_inner_greedy(ctx, pi, to_maximize,
                                                out_values, 1);
    testcase_t* current_testcase = &ctx->testcases.data[0];
    // // detect the strcmp pattern
    // if (__detect_strcmp_pattern(ctx, to_maximize, tmp_input)) {
    //     __vals_long_to_char(tmp_input, tmp_proof, *out_len);
    //     *out_values       = tmp_proof;
    //     unsigned long res = Z3_custom_eval(ctx->z3_ctx, to_maximize,
    //     tmp_input,
    //                                        current_testcase->value_sizes,
    //                                        current_testcase->values_len);
    //     return res;
    // }

    Z3_ast  original_to_maximize = to_maximize;
    Z3_sort arg_sort             = Z3_get_sort(ctx->z3_ctx, to_maximize);
    assert(Z3_get_sort_kind(ctx->z3_ctx, arg_sort) == Z3_BV_SORT &&
           "z3fuzz_minimize requires a BV sort");
    unsigned sort_size = Z3_get_bv_sort_size(ctx->z3_ctx, arg_sort);
    assert(sort_size > 1 && "z3fuzz_minimize unexpected sort size");

    if (sort_size < 64) {
        to_maximize = Z3_mk_sign_ext(ctx->z3_ctx, 64 - sort_size, to_maximize);
        sort_size   = 64;
    }

    eval_wapper_ctx_t ew;

    to_maximize    = Z3_mk_bvneg(ctx->z3_ctx, to_maximize);
    int valid_eval = __gd_init_eval(ctx, pi, to_maximize, 0, 1, &ew);
    if (!valid_eval) {
        // all inputs are fixed
        unsigned long res = ctx->model_eval(
            ctx->z3_ctx, original_to_maximize, tmp_input,
            current_testcase->value_sizes, current_testcase->values_len);
        __vals_long_to_char(tmp_input, tmp_proof,
                            current_testcase->testcase_len);
        *out_values = tmp_proof;
        return res;
    }

    eval_set_ctx(&ew);

    unsigned long max_val;
    gd_minimize(__gd_eval, ew.input, ew.input, &max_val, ew.mapping_size);

    __gd_fix_tmp_input(ew.input);
    max_val = ctx->model_eval(ctx->z3_ctx, original_to_maximize, tmp_input,
                              current_testcase->value_sizes,
                              current_testcase->values_len);
    __vals_long_to_char(tmp_input, tmp_proof, *out_len);
    *out_values = tmp_proof;

    __gd_free_eval(&ew);
    memcpy(tmp_input, current_testcase->values,
           current_testcase->values_len * sizeof(unsigned long));
    return max_val;
}

unsigned long z3fuzz_minimize(fuzzy_ctx_t* ctx, Z3_ast pi, Z3_ast to_minimize,
                              unsigned char const** out_values,
                              unsigned long*        out_len)
{
    memcpy(tmp_input, ctx->testcases.data[0].values,
           ctx->testcases.data[0].values_len * sizeof(unsigned long));

    *out_len = ctx->testcases.data[0].testcase_len;
    if (use_greedy_mamin)
        return __minimize_maximize_inner_greedy(ctx, pi, to_minimize,
                                                out_values, 0);
    testcase_t* current_testcase = &ctx->testcases.data[0];

    Z3_sort arg_sort = Z3_get_sort(ctx->z3_ctx, to_minimize);
    assert(Z3_get_sort_kind(ctx->z3_ctx, arg_sort) == Z3_BV_SORT &&
           "z3fuzz_minimize requires a BV sort");
    unsigned sort_size = Z3_get_bv_sort_size(ctx->z3_ctx, arg_sort);
    assert(sort_size > 1 && "z3fuzz_minimize unexpected sort size");

    if (sort_size < 64) {
        to_minimize = Z3_mk_sign_ext(ctx->z3_ctx, 64 - sort_size, to_minimize);
        sort_size   = 64;
    }

    eval_wapper_ctx_t ew;
    int valid_eval = __gd_init_eval(ctx, pi, to_minimize, 0, 1, &ew);
    if (!valid_eval) {
        // all inputs are fixed
        unsigned long res = ctx->model_eval(ctx->z3_ctx, to_minimize, tmp_input,
                                            current_testcase->value_sizes,
                                            current_testcase->values_len);
        __vals_long_to_char(tmp_input, tmp_proof,
                            current_testcase->testcase_len);
        *out_values = tmp_proof;
        return res;
    }
    eval_set_ctx(&ew);

    unsigned long min_val;
    gd_minimize(__gd_eval, ew.input, ew.input, &min_val, ew.mapping_size);

    __gd_fix_tmp_input(ew.input);
    __vals_long_to_char(tmp_input, tmp_proof, *out_len);
    *out_values = tmp_proof;

    __gd_free_eval(&ew);
    return min_val;
}

void z3fuzz_notify_constraint(fuzzy_ctx_t* ctx, Z3_ast constraint)
{
    // this is a visit of the AST of the constraint... Too slow? I don't know
    if (unlikely(skip_notify))
        return;

    ctx->stats.num_univocally_defined +=
        __check_univocally_defined(ctx, constraint, &ast_data);
}

int z3fuzz_get_optimistic_sol(fuzzy_ctx_t* ctx, unsigned char const** proof,
                              unsigned long* proof_size)
{
    if (opt_found) {
        testcase_t* t = &ctx->testcases.data[0];
        *proof_size   = t->testcase_len;
        *proof        = tmp_opt_proof;
    }
    return opt_found;
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

unsigned long z3fuzz_evaluate_expression_z3(fuzzy_ctx_t* ctx, Z3_ast query,
                                            Z3_ast* values)
{
    // evaluate query using [input <- input_val] as interpretation

    // build a model and assign an interpretation for the input symbols
    unsigned long res;
    Z3_model      z3_m = Z3_mk_model(ctx->z3_ctx);
    Z3_model_inc_ref(ctx->z3_ctx, z3_m);
    testcase_t* current_testcase = &ctx->testcases.data[0];

    unsigned i;
    for (i = 0; i < current_testcase->values_len; ++i) {
        unsigned int index = i;
        Z3_sort      sort =
            Z3_mk_bv_sort(ctx->z3_ctx, current_testcase->value_sizes[i]);
        Z3_symbol    s    = Z3_mk_int_symbol(ctx->z3_ctx, index);
        Z3_func_decl decl = Z3_mk_func_decl(ctx->z3_ctx, s, 0, NULL, sort);
        Z3_add_const_interp(ctx->z3_ctx, z3_m, decl, values[index]);
    }

    // evaluate the query in the model
    Z3_ast  solution;
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
