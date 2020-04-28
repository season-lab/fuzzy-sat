#include "timer.h"

#ifndef likely
#define likely(x) __builtin_expect(!!(x), 1)
#endif
#ifndef unlikely
#define unlikely(x) __builtin_expect(!!(x), 0)
#endif

static struct timeval stop;

static inline unsigned long compute_time_msec(struct timeval* start,
                                              struct timeval* end)
{
    return ((end->tv_sec - start->tv_sec) * 1000000 + end->tv_usec -
            start->tv_usec) /
           1000;
}

void init_timer(simple_timer_t* t, uint64_t time_max_msec)
{
    t->time_max_msec = time_max_msec;
}

void start_timer(simple_timer_t* t) { gettimeofday(&t->start, 0); }

int check_timer(simple_timer_t* t)
{
    static int i = 0;
    if (unlikely(++i & 64)) {
        i = 0;
        gettimeofday(&stop, 0);
        unsigned long delta_time = compute_time_msec(&t->start, &stop);
        if (delta_time > t->time_max_msec)
            return 1;
    }
    return 0;
}
