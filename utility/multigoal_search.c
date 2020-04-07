#include "multigoal_search.h"
#include "z3-fuzzy.h"

#define APROX_CONST 10

static fuzzy_ctx_t* ctx = NULL;

void mgs_init(fuzzy_ctx_t* fctx) { ctx = fctx; }
void mgs_free() {}

static bool is_const_type(Z3_ast c)
{
    /*
        check if "c" matches f(x) OP const
     */
    return false;
}

static void approx_linear(Z3_ast const_lhs, uint64_t cnst, uint64_t* x0,
                          uint64_t* coeff_out, uint32_t n_x)
{
    uint64_t* x1 = malloc(sizeof(uint64_t) * n_x);
    uint32_t  i;
    for (i = 0; i < n_x; ++i) {
        uint64_t f_lhs_x0 = ctx->model_eval(
            ctx->z3_ctx, const_lhs, x0, ctx->testcases.data[0].values_len, n_x);

        x1[i]             = x0[i] + APROX_CONST;
        uint64_t f_lhs_x1 = ctx->model_eval(
            ctx->z3_ctx, const_lhs, x1, ctx->testcases.data[0].values_len, n_x);

        coeff_out[i] =
            ((f_lhs_x1 - cnst) - (f_lhs_x0 - cnst)) / (x1[i] - x0[i]);
    }
    free(x1);
}

void mgs_solve(Z3_ast* constraints, uint32_t n_c, uint64_t* x0, uint64_t* x_res,
               uint32_t n_x)
{
    // pass
}
