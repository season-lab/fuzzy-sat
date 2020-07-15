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

def parse_file(filename):
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
	return tot_queries, n_fuzzy_faster, t_time_fuzzy, t_time_z3, t_sat_fuzzy, t_sat_z3, n_fuzzy_sat_z3_unknown

if len(sys.argv) < 2:
	usage()

dirname = sys.argv[1]

for filename in sorted(list(iterate_files(dirname))):
	if "queries" not in os.path.basename(filename):
		continue

	progname = os.path.basename(filename).split("-")[0]
	tot_queries, n_fuzzy_faster, t_time_fuzzy, t_time_z3, t_sat_fuzzy, t_sat_z3, n_fuzzy_sat_z3_unknown = parse_file(filename)
	print("%s;%d;%d;%.02f;%.03f;%.03f;%.02f;%d;%d;%.02f;%d" %
		(
			progname, tot_queries, n_fuzzy_faster, n_fuzzy_faster / tot_queries * 100,
			t_time_fuzzy, t_time_z3, t_time_z3 / t_time_fuzzy, t_sat_fuzzy, t_sat_z3,
			(t_sat_fuzzy - n_fuzzy_sat_z3_unknown) / t_sat_z3 * 100, n_fuzzy_sat_z3_unknown
		)
	)
