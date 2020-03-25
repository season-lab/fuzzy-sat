#ifndef GRADIENT_DESCEND_H
#define GRADIENT_DESCEND_H

#include <stdint.h>

void gd_init();
void gd_free();

void gd_minimize(uint64_t (*function)(uint64_t*), uint64_t* x0,
                 uint64_t* out_x_min, uint64_t* out_f_min, uint32_t n);
void gd_maximize(uint64_t (*function)(uint64_t*), uint64_t* x0,
                 uint64_t* out_x_max, uint64_t* out_f_max, uint32_t n);

#endif