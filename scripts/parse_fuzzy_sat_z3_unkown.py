#!/usr/bin/env python3

import shutil
import sys
import os

def usage():
	print("%s <dirname_exp> <dirname_queries>" % sys.argv[0])
	exit(1)

def iterate_files(path):
    for subdir, _, files in os.walk(path):
        for file in files:
            yield os.path.join(subdir, file)
        break

def unzip_queries(queries_dir, progname):
	zip_name = os.path.join(queries_dir, progname + "_queries.tar.gz")
	os.system("tar xzf %s -C /tmp/" % zip_name)

def prepare_output_for_progname(progname):
	os.system("mkdir /dev/shm/%s" % progname)

def copy_query(progname, query_n, time_z3, time_fuzzy):
	match = None
	for q in iterate_files("/tmp/%s_queries/" % progname):
		if "_%03d_" % query_n in q:
			match = q
			break

	assert match is not None
	shutil.copy2(
		match, 
		os.path.join("/dev/shm/%s" % progname, "query_%08d_%08d.smt2" % (int(time_z3 * 1000), int(time_fuzzy * 1000))))

def clean_tmp(progname):
	os.system("rm -rf /tmp/%s_queries" % progname)

def get_queries(dirname):
	queries     = {}
	tmp_expname = ""
	tmp_list    = []
	for filename in sorted(list(iterate_files(dirname))):
		if "queries" not in os.path.basename(filename):
			continue

		progname = os.path.basename(filename).split("-")[0]
		if "-fuzzy-" in os.path.basename(filename):
			assert tmp_expname == ""
			with open(filename, "r") as fin:
				fin.readline()
				for line in fin:
					t, sat = line.strip().split(",")
					tmp_list.append(
						[float(t), sat]
					)
			tmp_expname = progname

		if "-z3-" in os.path.basename(filename):
			assert tmp_expname != ""
			with open(filename, "r") as fin:
				fin.readline()
				i = 0
				for line in fin:
					t, sat = line.strip().split(",")
					tmp_list[i].extend(
						[float(t), sat]
					)
					i += 1
			assert tmp_expname not in queries
			queries[tmp_expname] = tmp_list
			tmp_expname = ""
			tmp_list = []
	return queries


def parse_queries(queries, progname):
	t_sat_fuzzy		= 0
	t_sat_z3		= 0
	t_time_fuzzy	= 0.0
	t_time_z3		= 0.0

	n_fuzzy_sat_z3_unknown	= 0
	n_fuzzy_faster			= 0
	tot_queries				= 0

	i = 0
	for q in queries:
		time_fuzzy, res_fuzzy, time_z3, res_z3 = q

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
			copy_query(progname, i, 0, time_fuzzy)
		elif float(time_z3) > 1000 and res_z3 == "sat" and res_fuzzy == "sat":
			copy_query(progname, i, time_z3, time_fuzzy)

		i += 1

if len(sys.argv) < 3:
	usage()

dirname = sys.argv[1]
queries_dir = sys.argv[2]

queries = get_queries(dirname)

for progname in sorted(list(queries.keys())):
	unzip_queries(queries_dir, progname)
	prepare_output_for_progname(progname)

	q = queries[progname]
	parse_queries(q, progname)

	clean_tmp(progname)
