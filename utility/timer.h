#ifndef TIMER_H
#define TIMER_H

#include <sys/time.h>
#include <stdint.h>

typedef struct simple_timer_t {
    struct timeval start;
    uint64_t       time_max_msec;
} simple_timer_t;

void init_timer(simple_timer_t* t, uint64_t time_max_msec);
void start_timer(simple_timer_t* t);
int  check_timer(simple_timer_t* t);

#endif