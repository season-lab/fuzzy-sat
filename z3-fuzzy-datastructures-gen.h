// *********** index group set ***********
#define MAX_GROUP_SIZE 8

typedef struct index_group_t {
    unsigned char n;                       // number of valid indexes
    unsigned long indexes[MAX_GROUP_SIZE]; // indexes
} index_group_t;

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
    return *((unsigned long*)&el->digest);
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