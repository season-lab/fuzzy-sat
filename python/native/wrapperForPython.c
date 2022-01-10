#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
#include "../../lib/z3-fuzzy.h"

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

static uint64_t* uptoOutBuffer  = NULL;
static uint32_t  uptoCounter    = 0;
static uint32_t  uptoMaxCounter = 0;

static fuzzy_findall_res_t evalUptoCallback(unsigned char const* out_bytes,
                                            unsigned long        out_bytes_len,
                                            unsigned long        val)
{
    assert(uptoOutBuffer);

    uptoOutBuffer[uptoCounter++] = val;
    if (uptoCounter >= uptoMaxCounter)
        return Z3FUZZ_STOP;
    return Z3FUZZ_GIVE_NEXT;
}

#define GD_MODE_NO_GD 0
#define GD_MODE_TOMIN 1
#define GD_MODE_TOMAX 2

uint32_t evalUpto(fuzzy_ctx_t* fctx, Z3_ast expr, Z3_ast pi, uint64_t* out,
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
