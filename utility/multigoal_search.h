#ifndef MULTIGOAL_SEARCH_H
#define MULTIGOAL_SEARCH_H

#include <z3.h>

void mgs_init();
void mgs_free();

void mgs_solve(Z3_ast* constraints, uint32_t n_c, uint64_t* x0, uint64_t* x_res, uint32_t n_x);

#endif