#ifndef TESTCASE_LIST_H
#define TESTCASE_LIST_H

#include <z3.h>

typedef struct testcase_t {
    unsigned char* bytes;
    Z3_ast*        z3_bytes;
    unsigned long  len;
} testcase_t;

#define DA_DATA_T testcase_t
#include "dynamic-array.h"

typedef da__testcase_t testcase_list_t;

void init_testcase_list(testcase_list_t* t);
void free_testcase_list(Z3_context ctx, testcase_list_t* t);
void load_testcase_folder(testcase_list_t* t, char* testcase_dir,
                          Z3_context ctx);
void load_testcase(testcase_list_t* t, char const* filename, Z3_context ctx);

#endif
