#!/usr/bin/env python3

from functools import reduce
import random
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

def get_queries(filename):
    res = []

    f = open(filename, "r")
    f.readline()
    for line in f:
        line = line.strip()
        t_fuzzy, sat_fuzzy, t_z3, sat_z3 = line.split(",")
        t_fuzzy = float(t_fuzzy)
        t_z3    = float(t_z3)
        res.append(
            (t_fuzzy, sat_fuzzy, t_z3, sat_z3)
        )
    f.close()

    return res

def get_time_fuzzy(queries):
    tot = 0.0

    for q in queries:
        t, _, _, _ = q
        tot += t

    return tot

def get_n_sat_fuzzy(queries):
    tot = 0

    for q in queries:
        _, sat, _, _ = q
        if sat == "sat":
            tot += 1

    return tot

def get_sat_z3_up_to_time(queries, time_max):
    tot_time = 0.0
    tot_sat = 0

    for q in queries:
        _, _, t, sat = q
        t = float(t)
        tot_time += t
        if tot_time > time_max:
            break
        if sat == "sat":
            tot_sat += 1

    return tot_sat

if len(sys.argv) < 2:
    usage()

dirname = sys.argv[1]

print("progname,time fuzzy,sat fuzzy,sat z3 [min],sat z3 [max],sat z3 [avg]")
for file in sorted(list(iterate_files(dirname))):
    if "queries" not in os.path.basename(file):
        continue

    progname = os.path.basename(file).split("-")[0]
    print(progname, end=",")
    queries = get_queries(file)
    time_fuzzy = get_time_fuzzy(queries)
    n_sat_fuzzy = get_n_sat_fuzzy(queries)
    
    avg_sat_z3 = 0.0
    min_sat_z3 = 9999999
    max_sat_z3 = 0
    i = 10000
    while i > 0:
        random.shuffle(queries)
        n_sat_z3 = get_sat_z3_up_to_time(queries, time_fuzzy)
        if n_sat_z3 > max_sat_z3:
            max_sat_z3 = n_sat_z3
        if n_sat_z3 < min_sat_z3:
            min_sat_z3 = n_sat_z3
        avg_sat_z3 += n_sat_z3
        i -= 1
    
    avg_sat_z3 /= 10000
    
    print("%.03f s,%d,%d,%d,%.03f" % (time_fuzzy / 1000, n_sat_fuzzy, min_sat_z3, max_sat_z3, avg_sat_z3))
