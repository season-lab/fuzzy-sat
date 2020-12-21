#include "wrapped_interval.h"
#include <stdio.h>

int main()
{
    wrapped_interval_t wi1 = wi_init(8);
    wi_update_add(&wi1, 10);
    wi_print(&wi1);

    printf("contains %d ? %d\n", 9, wi_contains_element(&wi1, 9));
    printf("contains %d ? %d\n", 10, wi_contains_element(&wi1, 10));
    printf("contains %d ? %d\n", 255, wi_contains_element(&wi1, 255));

    wi_update_cmp(&wi1, -4, OP_SGT);
    wi_print(&wi1);

    wi_update_sub(&wi1, 13);
    wi_print(&wi1);

    wi_update_add(&wi1, 30);
    wi_print(&wi1);

    wrapped_interval_t wi2 = wi_init(8);
    wi_update_cmp(&wi2, 0xb0, OP_UGT);
    wi_update_sub(&wi2, 0x0a);
    wi_print(&wi2);

    wrapped_interval_t wi3 = wi_init(32);
    wi_update_cmp(&wi3, 0xbbbbbbbb, OP_ULT);
    wi_update_sub(&wi3, 0xaaaaaaaa);
    wi_print(&wi3);
}