#include "utility/interval.h"
#include <assert.h>

int main()
{
    interval_t iu8 = init_interval(8);
    assert(update_interval(&iu8, 7, OP_ULT) == 1);
    print_interval(&iu8);

    interval_t is8 = init_interval(8);
    assert(update_interval(&is8, 7, OP_SLT) == 1);
    print_interval(&is8);

    interval_t iu64 = init_interval(64);
    assert(update_interval(&iu64, 100, OP_UGT) == 1);
    print_interval(&iu64);

    interval_t is64 = init_interval(64);
    assert(update_interval(&is64, 100, OP_SGT) == 1);
    print_interval(&is64);

    iu64 = init_interval(64);
    assert(update_interval(&iu64, 100, OP_ULT) == 1);
    print_interval(&iu64);

    is64 = init_interval(64);
    assert(update_interval(&is64, 100, OP_SLT) == 1);
    print_interval(&is64);

    iu64 = init_interval(64);
    assert(update_interval(&iu64, 30, OP_UGE) == 1);
    assert(update_interval(&iu64, 51, OP_ULT) == 1);
    assert(update_interval(&iu64, 10, OP_ULT) == 0);
    print_interval(&iu64);
}