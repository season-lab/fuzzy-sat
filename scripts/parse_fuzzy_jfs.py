#!/usr/bin/env python3

import sys
import os

def usage():
    print("%s <dirname>" % sys.argv[0])
    exit(1)

def iterate_files(path):
    for subdir, _, files in os.walk(path):
        for file in files:
            yield os.path.join(subdir, file)
        break

def get_queries(dirname):
    queries     = {}
    tmp_expname = ""
    tmp_list    = []
    for filename in sorted(list(iterate_files(dirname))):
        progname = os.path.basename(filename).split("-")[0]
        if "-fuzzy" in os.path.basename(filename):
            assert tmp_expname == ""
            with open(filename, "r") as fin:
                fin.readline()
                for line in fin:
                    sat, t = line.strip().split(",")
                    tmp_list.append(
                        [float(t), int(sat)]
                    )
            tmp_expname = progname

        if "-jfs" in os.path.basename(filename):
            assert tmp_expname != ""
            with open(filename, "r") as fin:
                fin.readline()
                i = 0
                for line in fin:
                    sat, t = line.strip().split(",")
                    tmp_list[i].extend(
                        [float(t), int(sat)]
                    )
                    i += 1
            assert tmp_expname not in queries
            queries[tmp_expname] = tmp_list
            tmp_expname = ""
            tmp_list = []
    return queries

def parse_queries(queries):
    t_sat_fuzzy     = 0
    t_sat_jfs       = 0
    t_time_fuzzy    = 0.0
    t_time_jfs      = 0.0

    n_jfs_sat_fuzzy_unkn  = 0
    tot_queries           = 0

    for q in queries:
        time_fuzzy, res_fuzzy, time_jfs, res_jfs = q

        tot_queries += 1
        t_sat_fuzzy += res_fuzzy
        t_sat_jfs   += res_jfs

        t_time_fuzzy += float(time_fuzzy)
        t_time_jfs   += float(time_jfs)

        if res_fuzzy == 0 and res_jfs == 1:
            n_jfs_sat_fuzzy_unkn += 1

    return tot_queries, t_time_fuzzy, t_time_jfs, t_sat_fuzzy, t_sat_jfs, n_jfs_sat_fuzzy_unkn

if len(sys.argv) < 2:
    usage()

dirname = sys.argv[1]
queries = get_queries(dirname)

for progname in sorted(list(queries.keys())):
    q = queries[progname]
    tot_queries, t_time_fuzzy, t_time_jfs, t_sat_fuzzy, t_sat_jfs, n_jfs_sat_fuzzy_unkn = parse_queries(q)
    print("%s;%d;%d;%d;%.02f;%d;%d;%d" %
        (
            progname, tot_queries, t_time_fuzzy, t_time_jfs, t_time_jfs / t_time_fuzzy, t_sat_fuzzy,
            t_sat_jfs, n_jfs_sat_fuzzy_unkn
        )
    )
