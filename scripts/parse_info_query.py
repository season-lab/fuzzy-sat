#!/usr/bin/env python3

import sys

def usage():
	print("%s <data.csv>" % sys.argv[0])
	exit(1)

if len(sys.argv) < 2:
	usage()

filename = sys.argv[1]
f = open(filename, "r")

t_sat_fuzzy		= 0
t_sat_z3		= 0
t_time_fuzzy	= 0.0
t_time_z3		= 0.0

n_fuzzy_sat_z3_unknown	= 0
n_fuzzy_faster			= 0
tot_queries				= 0

f.readline()
for line in f:
	line = line.strip()
	time_fuzzy, res_fuzzy, time_z3, res_z3 = line.split(",")

	tot_queries += 1
	if res_fuzzy == "sat":
		t_sat_fuzzy += 1
	if res_z3 == "sat":
		t_sat_z3 += 1

	t_time_fuzzy	+= float(time_fuzzy)
	t_time_z3		+= float(time_z3)

	if float(time_fuzzy) < float(time_z3):
		n_fuzzy_faster += 1
	if res_z3 == "unknown" and res_fuzzy == "sat":
		n_fuzzy_sat_z3_unknown += 1

f.close()

# tot queries, n fuzzy faster, perc fuzzy faster, tot time fuzzy, tot time z3, speedup fuzzy, n sat fuzzy, n sat z3, accuracy, n fuzzy but z3 timeout
print("%d;%d;%.02f %%;%.03f msec;%.03f msec;%.02f x;%d;%d;%.02f %%;%d\n" % \
	(
		tot_queries, n_fuzzy_faster, n_fuzzy_faster / tot_queries * 100,
		t_time_fuzzy, t_time_z3, t_time_z3 / t_time_fuzzy, 
		t_sat_fuzzy, t_sat_z3, t_sat_fuzzy / t_sat_z3 * 100,
		n_fuzzy_sat_z3_unknown
	))