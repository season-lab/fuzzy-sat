#!/usr/bin/env python3

import z3
import os
import re
import sys

def get_queries(filename):
	queries = z3.parse_smt2_file(filename)
	return queries

def get_faster_fuzzy(csv_filename):
	with open(csv_filename, "r") as fin:
		lines = fin.readlines()

	lines = lines[1:]
	ids = set()
	i = 0
	for line in lines:
		line = line.strip()
		split = line.split(",")
		if split[1] == "sat" and split[3] == "unknown":
			ids.add(i)
		i += 1

	return ids

def get_times(csv_filename, ids):
	with open(csv_filename, "r") as fin:
		lines = fin.readlines()

	times = []
	lines = lines[1:]
	for idx in ids:
		line = lines[idx].strip()
		split = line.split(",")
		times.append(
			(split[0], split[2])
		)
	return times

def find_inputs(query):
    inputs = re.findall(r"k![0-9]+", query.sexpr().replace("\n", ""))
    return set(inputs)

def usage():
	print("%s <csv_filename> <smt2_file> <out_dir>" % sys.argv[0])
	exit(1)

if len(sys.argv) < 4:
	usage()

csv_filename = sys.argv[1]
smt2_file    = sys.argv[2]
out_dir      = sys.argv[3]

if not os.path.exists(out_dir):
    os.mkdir(out_dir)

queries = get_queries(smt2_file)
ids = get_faster_fuzzy(csv_filename)

i = 0
for idx in ids:
    query = queries[idx]
    filename = "query_%03d.smt2" % i
    fout = open(out_dir + "/" + filename, "w")
    for inp in find_inputs(query):
        fout.write("(declare-const %s (_ BitVec 8))\n" % inp)
    fout.write("(assert \n" + query.sexpr() + "\n)\n(check-sat)")
    fout.close()
    i += 1

i = 0
times = get_times(csv_filename, ids)
fout = open(out_dir + "/times.txt", "w")
fout.write("#q\tfuzzy\tz3\n")
for time_fuzzy, time_z3 in times:
	fout.write("%d\t%s\t%s\n" % (i, time_fuzzy, time_z3))
	i += 1
