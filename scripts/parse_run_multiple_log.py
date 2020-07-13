#!/usr/bin/env python3

import sys

def usage():
    print("%s <log-fuzzy> <log-jsf>" % sys.argv[0])
    exit(1)

if len(sys.argv) < 3:
    usage()

log_fuzzy = sys.argv[1]
log_jsf = sys.argv[2]

f_fuzzy = open(log_fuzzy, "r")
f_jsf = open(log_jsf, "r")

tot_t_fuzzy = 0.0
n_sat_fuzzy = 0
fuzzy_sat_dict = {}

i = 0
for line in f_fuzzy:
    sat_fuzzy, t_fuzzy = line.split(",")
    t_fuzzy = float(t_fuzzy)

    if sat_fuzzy == "1":
        n_sat_fuzzy += 1
        fuzzy_sat_dict[i] = True
    else:
        fuzzy_sat_dict[i] = False
    tot_t_fuzzy += t_fuzzy
    i += 1

tot_t_jsf = 0.0
n_sat_jsf = 0
jfs_sat_but_no_fuzzy = 0

i = 0
for line in f_jsf:
    sat_jsf, t_jsf = line.split(",")
    t_jsf = float(t_jsf)

    if sat_jsf == "1":
        n_sat_jsf += 1
        if not fuzzy_sat_dict[i]:
            jfs_sat_but_no_fuzzy += 1
    tot_t_jsf += t_jsf
    i += 1

f_fuzzy.close()
f_jsf.close()

print("tot time fuzzy:", tot_t_fuzzy)
print("tot time jsf:  ", tot_t_jsf)
print("num sat fuzzy: ", n_sat_fuzzy)
print("num sat jsf:   ", n_sat_jsf)
print("jsf sat but no fuzzy: ", jfs_sat_but_no_fuzzy)