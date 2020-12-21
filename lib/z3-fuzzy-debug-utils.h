static inline void print_index_queue(ast_info_ptr data)
{
    index_group_t* group;
    fprintf(stderr, "----- QUEUE -----\n");
    unsigned int i, j;
    i = 0;
    set_reset_iter__index_group_t(&data->index_groups, 1);
    while (set_iter_next__index_group_t(&data->index_groups, 1, &group)) {
        for (j = 0; j < group->n; ++j)
            fprintf(stderr, "group: %d. index: 0x%lx\n", i, group->indexes[j]);
        i++;
    }

    fprintf(stderr, "\n\n");

    ulong* p;
    set_reset_iter__ulong(&data->indexes, 1);
    while (set_iter_next__ulong(&data->indexes, 1, &p))
        fprintf(stderr, "index: 0x%lx\n", *p);

    fprintf(stderr, "-----------------\n");
}

static inline void print_index_group(index_group_t* ig)
{
    fprintf(stderr,
            "IG {\n"
            "  n: %u\n"
            "  indexes: ",
            ig->n);
    unsigned i;
    for (i = 0; i < ig->n; ++i)
        fprintf(stderr, "%03ld ", ig->indexes[i]);
    fprintf(stderr, "\n}\n");
}

static inline void print_interval_groups(fuzzy_ctx_t* ctx)
{
    fprintf(stderr, "----- INTERVAL GROUPS -----\n");
    set__interval_group_ptr* group_intervals =
        (set__interval_group_ptr*)ctx->group_intervals;

    interval_group_ptr* el;
    set_reset_iter__interval_group_ptr(group_intervals, 0);
    while (set_iter_next__interval_group_ptr(group_intervals, 0, &el)) {
        fprintf(stderr, "***************************\n");
        print_index_group(&(*el)->group);
        wi_print(&(*el)->interval);
        fprintf(stderr, "***************************\n");
    }
    fprintf(stderr, "------------------------------\n");
}

static inline void print_univocally_defined(fuzzy_ctx_t* ctx)
{
    fprintf(stderr, "----- UNIVOCALLY DEFINED -----\n");
    set__ulong* univocally_defined_inputs =
        (set__ulong*)ctx->univocally_defined_inputs;

    ulong* p;
    set_reset_iter__ulong(univocally_defined_inputs, 0);
    while (set_iter_next__ulong(univocally_defined_inputs, 0, &p)) {
        fprintf(stderr, "> 0x%lx\n", *p);
    }

    fprintf(stderr, "------------------------------\n");
}