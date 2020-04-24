#ifndef SET_H
#define SET_H

#include <strings.h>

typedef struct set_iter_t {
    // unsigned free;  // TODO I should implement this
    unsigned long iter_buck_id;
    unsigned long iter_el_in_buck_id;
} set_iter_t;

#define NUM_ITERATORS 2

#endif

#ifndef SET_N_BUCKETS
#define SET_N_BUCKETS 1024
#endif

#ifndef glue
#define xglue(x, y) x##y
#define glue(x, y) xglue(x, y)
#endif

#ifndef SET_DATA_T
#define SET_DATA_T long
#endif

#define DA_DATA_T SET_DATA_T
#define DA_INIT_SIZE 5
#include "dynamic-array.h"

typedef struct glue(set__, SET_DATA_T)
{
    unsigned long (*hash)(SET_DATA_T*);
    unsigned int (*equals)(SET_DATA_T*, SET_DATA_T*);
    glue(da__, SET_DATA_T) * buckets;
    unsigned long* filled_buckets;
    unsigned long  filled_buckets_i;
    unsigned long  size;
    set_iter_t     iterators[NUM_ITERATORS];
}
glue(set__, SET_DATA_T);

static inline void glue(set_init__, SET_DATA_T)(
    glue(set__, SET_DATA_T) * set, unsigned long (*hash_function)(SET_DATA_T*),
    unsigned int (*equals)(SET_DATA_T*, SET_DATA_T*))
{
    set->hash             = hash_function;
    set->equals           = equals;
    set->filled_buckets_i = 0;
    set->size             = 0;
    memset(set->iterators, 0, sizeof(set_iter_t) * NUM_ITERATORS);
    set->buckets = (glue(da__, SET_DATA_T)*)malloc(
        sizeof(glue(da__, SET_DATA_T)) * SET_N_BUCKETS);
    assert(set->buckets != 0 && "set set_init() - malloc failed");
    set->filled_buckets =
        (unsigned long*)malloc(sizeof(unsigned long) * SET_N_BUCKETS);
    assert(set->filled_buckets != 0 && "set set_init() - malloc failed");

    // this memset is crucial
    memset(set->buckets, 0, sizeof(glue(da__, SET_DATA_T)) * SET_N_BUCKETS);
}

static inline void glue(set_add__, SET_DATA_T)(glue(set__, SET_DATA_T) * set,
                                               SET_DATA_T el)
{
    unsigned long el_hash   = set->hash((SET_DATA_T*)&el);
    unsigned long bucket_id = el_hash % SET_N_BUCKETS;

    // printf("se_add() hash=%lu, buck_id=%lu\n", el_hash, bucket_id);

    glue(da__, SET_DATA_T)* bucket = &set->buckets[bucket_id];

    if (bucket->data == NULL) {
        // uninitialized bucket
        set->filled_buckets[set->filled_buckets_i++] = bucket_id;
        glue(da_init__, SET_DATA_T)(bucket);
        glue(da_add_item__, SET_DATA_T)(bucket, el);
        set->size++;
    } else if (bucket->size == 0) {
        // initialized but empty (as a consequence of set_remove_all)
        set->filled_buckets[set->filled_buckets_i++] = bucket_id;
        glue(da_add_item__, SET_DATA_T)(bucket, el);
        set->size++;
    } else {
        // collision
        unsigned i, is_present = 0;
        for (i = 0; i < bucket->size; ++i) {
            SET_DATA_T* tmp = glue(da_get_ref_item__, SET_DATA_T)(bucket, i);
            if (set->hash((SET_DATA_T*)tmp) == el_hash &&
                set->equals((SET_DATA_T*)tmp, (SET_DATA_T*)&el)) {
                is_present = 1;
                break;
            }
        }
        if (!is_present) {
            glue(da_add_item__, SET_DATA_T)(bucket, el);
            set->size++;
        }
    }
}

static inline int glue(set_check__, SET_DATA_T)(glue(set__, SET_DATA_T) * set,
                                                SET_DATA_T el)
{
    unsigned long el_hash   = set->hash((SET_DATA_T*)&el);
    unsigned long bucket_id = el_hash % SET_N_BUCKETS;

    glue(da__, SET_DATA_T)* bucket = &set->buckets[bucket_id];

    if (bucket->data == 0) {
        return 0;
    }
    unsigned i, is_present = 0;
    for (i = 0; i < bucket->size; ++i) {
        SET_DATA_T* tmp = glue(da_get_ref_item__, SET_DATA_T)(bucket, i);
        if (set->equals((SET_DATA_T*)tmp, (SET_DATA_T*)&el)) {
            is_present = 1;
            break;
        }
    }
    return is_present;
}

static inline void glue(set_reset_iter__,
                        SET_DATA_T)(glue(set__, SET_DATA_T) * set,
                                    unsigned iterator_id)
{
    assert(iterator_id < NUM_ITERATORS &&
           "set_reset_iter() iterator_id overflow");
    set->iterators[iterator_id].iter_buck_id       = 0;
    set->iterators[iterator_id].iter_el_in_buck_id = 0;
}

static inline int glue(set_iter_next__,
                       SET_DATA_T)(glue(set__, SET_DATA_T) * set,
                                   unsigned iterator_id, SET_DATA_T** res)
{
    assert(iterator_id < NUM_ITERATORS &&
           "set_iter_next() iterator_id overflow");
    if (set->iterators[iterator_id].iter_buck_id >= set->filled_buckets_i)
        return 0;
    glue(da__, SET_DATA_T)* bucket =
        &set->buckets
             [set->filled_buckets[set->iterators[iterator_id].iter_buck_id]];
    if (set->iterators[iterator_id].iter_el_in_buck_id >= bucket->size) {
        set->iterators[iterator_id].iter_buck_id++;
        set->iterators[iterator_id].iter_el_in_buck_id = 0;
        return glue(set_iter_next__, SET_DATA_T)(set, iterator_id, res);
    }

    *res = glue(da_get_ref_item__, SET_DATA_T)(
        bucket, set->iterators[iterator_id].iter_el_in_buck_id);
    set->iterators[iterator_id].iter_el_in_buck_id++;
    return 1;
}

static inline SET_DATA_T* glue(set_find_el__,
                               SET_DATA_T)(glue(set__, SET_DATA_T) * set,
                                           SET_DATA_T* el)
{
    unsigned long el_hash   = set->hash(el);
    unsigned long bucket_id = el_hash % SET_N_BUCKETS;

    glue(da__, SET_DATA_T)* bucket = &set->buckets[bucket_id];

    if (bucket->data == 0) {
        return 0;
    }
    unsigned i;
    for (i = 0; i < bucket->size; ++i) {
        SET_DATA_T* tmp = glue(da_get_ref_item__, SET_DATA_T)(bucket, i);
        if (set->hash((SET_DATA_T*)tmp) == el_hash &&
            set->equals((SET_DATA_T*)tmp, (SET_DATA_T*)el))
            return tmp;
    }
    return 0;
}

// TODO I should implement a _get_free_iter_ and _release_iter_

static inline void glue(set_remove_all__,
                        SET_DATA_T)(glue(set__, SET_DATA_T) * set,
                                    void (*el_free)(SET_DATA_T*))
{
    unsigned long i;
    for (i = 0; i < set->filled_buckets_i; ++i)
        glue(da_remove_all__, SET_DATA_T)(&set->buckets[set->filled_buckets[i]],
                                          el_free);

    set->filled_buckets_i = 0;
    set->size             = 0;
}

static inline void glue(set_free__, SET_DATA_T)(glue(set__, SET_DATA_T) * set,
                                                void (*el_free)(SET_DATA_T*))
{
    unsigned long i;
    for (i = 0; i < set->filled_buckets_i; ++i)
        glue(da_free__, SET_DATA_T)(&set->buckets[set->filled_buckets[i]],
                                    el_free);
    free(set->buckets);
    free(set->filled_buckets);
    set->buckets        = NULL;
    set->filled_buckets = NULL;
    set->size           = 0;
}

#undef SET_DATA_T
#undef SET_N_BUCKETS
