#ifndef INTERVAL_H
#define INTERVAL_H

#include <stdint.h>

#define OP_ULT 0
#define OP_SLT 1
#define OP_ULE 2
#define OP_SLE 3
#define OP_UGT 4
#define OP_SGT 5
#define OP_UGE 6
#define OP_SGE 7

typedef int optype;

typedef struct interval_t {
    __int128_t min;
    __int128_t max;
    uint32_t   size;
} interval_t;

interval_t init_interval(unsigned size);
int        update_interval(interval_t* src, __int128_t c, optype op);
void       print_interval(interval_t* interval);

int      is_signed(interval_t* interval);
int64_t  get_signed_min(interval_t* interval);
int64_t  get_signed_max(interval_t* interval);
uint64_t get_unsigned_min(interval_t* interval);
uint64_t get_unsigned_max(interval_t* interval);
uint64_t get_range(interval_t* interval);

#endif