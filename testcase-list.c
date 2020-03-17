#include <fts.h>
#include <stdlib.h>
#include <assert.h>
#include "testcase-list.h"

#define TESTCASE_LIB_LOG(x...) fprintf(stderr, "[testcase-lib] " x)

void init_testcase_list(testcase_list_t* t) { da_init__testcase_t(t); }

void free_testcase_list(Z3_context ctx, testcase_list_t* t)
{
    unsigned int i, j;
    for (i = 0; i < t->size; ++i) {
        free(t->data[i].bytes);
        t->data[i].bytes = NULL;
        for (j = 0; j < t->data[i].len; ++j)
            Z3_dec_ref(ctx, t->data[i].z3_bytes[j]);
        free(t->data[i].z3_bytes);
        t->data[i].z3_bytes = NULL;
    }
    t->size = 0;
    da_free__testcase_t(t, NULL);
}

void load_testcase(testcase_list_t* t, char const* filename, Z3_context ctx)
{
    assert(t->size < t->max_size && "testcase_list is full\n");

    TESTCASE_LIB_LOG("Loading testcase \"%s\" \n", filename);

    testcase_t    tc = {0};
    FILE*         fp = fopen(filename, "r");
    int           res, i = 0;
    unsigned char c;

    assert(fp != NULL && "fopen() failed");

    fseek(fp, 0L, SEEK_END);
    tc.len = ftell(fp);
    fseek(fp, 0L, SEEK_SET);

    tc.bytes        = (unsigned char*)malloc(sizeof(unsigned char) * tc.len);
    tc.z3_bytes     = (Z3_ast*)malloc(sizeof(Z3_ast) * tc.len);
    Z3_sort bv_sort = Z3_mk_bv_sort(ctx, 8);

    while (1) {
        res = fread(&c, sizeof(char), 1, fp);
        if (res != 1)
            break;
        tc.bytes[i]    = c;
        tc.z3_bytes[i] = Z3_mk_unsigned_int(ctx, c, bv_sort);
        Z3_inc_ref(ctx, tc.z3_bytes[i]);
        i++;
    }
    da_add_item__testcase_t(t, tc);
    fclose(fp);
}

void load_testcase_folder(testcase_list_t* t, char* testcase_dir,
                          Z3_context ctx)
{
    FTS*        ftsp;
    FTSENT *    p, *chp;
    int         fts_options = FTS_LOGICAL | FTS_NOCHDIR;
    char* const file_list[] = {testcase_dir, NULL};

    TESTCASE_LIB_LOG("Loading testcases from folder \"%s\" \n", testcase_dir);

    ftsp = fts_open(file_list, fts_options, NULL);
    assert(ftsp != NULL && "error in fts_open");

    chp = fts_children(ftsp, 0);
    assert(chp != NULL && "error in fts_children");

    while ((p = fts_read(ftsp)) != NULL) {
        switch (p->fts_info) {
            case FTS_D:
                TESTCASE_LIB_LOG("found directory\t %s skipping\n",
                                 p->fts_path);
                break;
            case FTS_F:
                load_testcase(t, p->fts_path, ctx);
                break;
            default:
                break;
        }
    }
    fts_close(ftsp);
}
