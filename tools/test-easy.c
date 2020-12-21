#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>
#include "z3-fuzzy.h"

// #define DUMP_SAT_QUERIES
// #define DUMP_PROOFS

fuzzy_ctx_t fctx;

int main(int argc, char* argv[])
{
    Z3_config     cfg = Z3_mk_config();
    Z3_context    ctx = Z3_mk_context(cfg);
    Z3_ast const* proof;
    unsigned long proof_size;
    Z3_ast        query;
    Z3_sort       bsort = Z3_mk_bv_sort(ctx, 8);

    z3fuzz_init(&fctx, ctx, "query_db/simple.seed", NULL);

    Z3_symbol sk0 = Z3_mk_int_symbol(ctx, 0);
    Z3_ast    k0  = Z3_mk_const(ctx, sk0, bsort);
    Z3_symbol sk1 = Z3_mk_int_symbol(ctx, 1);
    Z3_ast    k1  = Z3_mk_const(ctx, sk1, bsort);
    Z3_symbol sk2 = Z3_mk_int_symbol(ctx, 2);
    Z3_ast    k2  = Z3_mk_const(ctx, sk2, bsort);
    Z3_symbol sk3 = Z3_mk_int_symbol(ctx, 3);
    Z3_ast    k3  = Z3_mk_const(ctx, sk3, bsort);

    query = Z3_mk_concat(ctx, k0, k1);
    query = Z3_mk_concat(ctx, query, k2);
    query = Z3_mk_concat(ctx, query, k3);

    query = Z3_mk_eq(ctx, query,
                     Z3_mk_unsigned_int(ctx, 42, Z3_mk_bv_sort(ctx, 32)));

    z3fuzz_query_check_light(&fctx, query, query, &proof, &proof_size);

    z3fuzz_free(&fctx);
    return 0;
}