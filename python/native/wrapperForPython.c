#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>
#include "../../lib/z3-fuzzy.h"

typedef struct {
    uint64_t val;
    uint8_t* proof;
    uint64_t proof_size;
} evalElement;

fuzzy_ctx_t* createFuzzyCtx(Z3_context ctx, char* seed_filename,
                            unsigned timeout)
{
    fuzzy_ctx_t* fctx = (fuzzy_ctx_t*)malloc(sizeof(fuzzy_ctx_t));
    z3fuzz_init(fctx, ctx, seed_filename, NULL, NULL, timeout);
    return fctx;
}

void destroyFuzzyCtx(fuzzy_ctx_t* fctx)
{
    z3fuzz_free(fctx);
    free(fctx);
}

evalElement* createEvalElementArray(size_t n_els, size_t proof_size)
{
    evalElement* res = (evalElement*)malloc(sizeof(evalElement) * n_els);
    size_t       i;
    for (i = 0; i < n_els; ++i) {
        res[i].val        = 0;
        res[i].proof      = (uint8_t*)malloc(proof_size);
        res[i].proof_size = proof_size;
    }

    return res;
}

void destroyEvalElementArray(evalElement* arr, size_t n_els)
{
    size_t i;
    for (i = 0; i < n_els; ++i)
        free(arr[i].proof);
    free(arr);
}

static evalElement* uptoOutBuffer  = NULL;
static uint32_t     uptoCounter    = 0;
static uint32_t     uptoMaxCounter = 0;

static fuzzy_findall_res_t evalUptoCallback(unsigned char const* out_bytes,
                                            unsigned long        out_bytes_len,
                                            unsigned long        val)
{
    assert(uptoOutBuffer);
    assert(uptoOutBuffer[uptoCounter].proof_size == out_bytes_len);

    uptoOutBuffer[uptoCounter].val = val;
    memcpy(uptoOutBuffer[uptoCounter].proof, out_bytes, out_bytes_len);

    uptoCounter++;
    if (uptoCounter >= uptoMaxCounter)
        return Z3FUZZ_STOP;
    return Z3FUZZ_GIVE_NEXT;
}

#define GD_MODE_NO_GD 0
#define GD_MODE_TOMIN 1
#define GD_MODE_TOMAX 2

uint32_t evalUpto(fuzzy_ctx_t* fctx, Z3_ast expr, Z3_ast pi, evalElement* out,
                  uint32_t out_len, uint8_t gd_mode)
{
    uptoOutBuffer  = out;
    uptoCounter    = 0;
    uptoMaxCounter = out_len;

    switch (gd_mode) {
        case GD_MODE_NO_GD:
            z3fuzz_find_all_values(fctx, expr, pi, evalUptoCallback);
            break;
        case GD_MODE_TOMIN:
            z3fuzz_find_all_values_gd(fctx, expr, pi, 1, evalUptoCallback);
            break;
        case GD_MODE_TOMAX:
            z3fuzz_find_all_values_gd(fctx, expr, pi, 0, evalUptoCallback);
            break;
        default:
            fprintf(stderr, "Unexpected gd_mode: %u\n", gd_mode);
            assert(0);
    }
    return uptoCounter;
}
