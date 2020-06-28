// *********** index group set ***********
#define MAX_GROUP_SIZE 8

typedef struct index_group_t {
    unsigned char n;                       // number of valid indexes
    unsigned long indexes[MAX_GROUP_SIZE]; // indexes
} index_group_t;

#define SET_N_BUCKETS 8
#define SET_DATA_T index_group_t
#include <set.h>
typedef set__index_group_t index_groups_t;

unsigned long index_group_hash(index_group_t* el)
{
    unsigned long a = el->n;
    unsigned long b = a > 0 ? el->indexes[0] : 0;
    return (a + b) * (a + b + 1) / 2;
}

unsigned int index_group_equals(index_group_t* el1, index_group_t* el2)
{
    if (el1->n != el2->n)
        return 0;

    unsigned char i;
    for (i = 0; i < el1->n; ++i)
        if (el1->indexes[i] != el2->indexes[i])
            return 0;
    return 1;
}
// ********* end index group set *********

// ************* indexes set *************
typedef unsigned long ulong;
#define SET_N_BUCKETS 512
#define SET_DATA_T ulong
#include <set.h>
unsigned long index_hash(unsigned long* el) { return *el; }
unsigned int  index_equals(unsigned long* el1, unsigned long* el2)
{
    return *el1 == *el2;
}
typedef set__ulong indexes_t;
// *********** end indexes set ***********

// ************* values array ************
typedef da__ulong values_t;
// *********** end values array **********

// *********** evaluate set **************
typedef struct digest_t {
    unsigned char digest[16];
} digest_t;

unsigned long digest_64bit_hash(digest_t* el)
{
    unsigned long* __attribute__((__may_alias__)) digest_p =
        ((unsigned long*)&el->digest);
    return *digest_p;
}

unsigned int digest_equals(digest_t* el1, digest_t* el2)
{
    unsigned i;
    for (i = 0; i < 16; ++i)
        if (el1->digest[i] != el2->digest[i])
            return 0;
    return 1;
}

#define SET_DATA_T digest_t
#include <set.h>

typedef set__digest_t processed_set_t;
// ********* end evaluate set ************
// ********* conflicting dict ************
typedef struct ast_ptr {
    Z3_context ctx;
    Z3_ast     ast;
} ast_ptr;
#define SET_DATA_T ast_ptr
#include <set.h>

typedef set__ast_ptr* conflicting_ptr;
#define DICT_DATA_T conflicting_ptr
#include <dict.h>

static void          ast_ptr_free(ast_ptr* el) { Z3_dec_ref(el->ctx, el->ast); }
static unsigned long ast_ptr_hash(ast_ptr* el)
{
    return Z3_get_ast_id(el->ctx, el->ast);
}
static unsigned int ast_ptr_equals(ast_ptr* el1, ast_ptr* el2)
{
    return Z3_get_ast_id(el1->ctx, el1->ast) ==
           Z3_get_ast_id(el2->ctx, el2->ast);
}

static inline void conflicting_init(conflicting_ptr ptr)
{
    set_init__ast_ptr(ptr, &ast_ptr_hash, &ast_ptr_equals);
}

static inline void conflicting_ptr_free(conflicting_ptr* ptr)
{
    set_free__ast_ptr(*ptr, ast_ptr_free);
    free(*ptr);
}

static inline void add_item_to_conflicting(dict__conflicting_ptr* dict,
                                           Z3_ast expr, unsigned long idx,
                                           Z3_context ctx)
{
    conflicting_ptr  el;
    conflicting_ptr* match = dict_get_ref__conflicting_ptr(dict, idx);
    if (match == NULL) {
        el = (conflicting_ptr)malloc(sizeof(set__ast_ptr));
        conflicting_init(el);
        dict_set__conflicting_ptr(dict, idx, el);
    } else
        el = *match;

    Z3_inc_ref(ctx, expr);
    ast_ptr v = {.ctx = ctx, .ast = expr};
    set_add__ast_ptr(el, v);
}
// ******** end conflicting dict *********
// ********** interval group *************
typedef struct interval_group_t {
    wrapped_interval_t interval;
    index_group_t      group;
} interval_group_t;

typedef interval_group_t* interval_group_ptr;
#define SET_DATA_T interval_group_ptr
#include <set.h>

#define DICT_DATA_T da__interval_group_ptr
#include <dict.h>

static unsigned long interval_group_ptr_hash(interval_group_ptr* el)
{
    return index_group_hash(&(*el)->group);
}

static unsigned int interval_group_ptr_equals(interval_group_ptr* el1,
                                              interval_group_ptr* el2)
{
    return index_group_equals(&(*el1)->group, &(*el2)->group);
}

static void interval_group_set_el_free(interval_group_ptr* el) { free(*el); }

static void index_to_group_intervals_el_free(da__interval_group_ptr* el)
{
    da_free__interval_group_ptr(el, NULL);
}
// ******* end interval group *************
