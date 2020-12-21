#ifndef GRADIENT_DESCEND_H
#define GRADIENT_DESCEND_H

#include <stdint.h>

void gd_init();
void gd_free();

int gd_minimize(uint64_t (*function)(uint64_t*, int*), uint64_t* x0,
                uint64_t* out_x_min, uint64_t* out_f_min, uint32_t n);

int gd_descend_transf(uint64_t (*function)(uint64_t*, int*), uint64_t* x0,
                      uint64_t* out_x, uint64_t* out_f, uint32_t n);
int gd_max_gradient(uint64_t (*function)(uint64_t*, int*), uint64_t* x0,
                    uint32_t n, uint64_t* v);

#endif