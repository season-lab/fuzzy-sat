#!/usr/bin/env python3

from functools import reduce
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

if len(sys.argv) < 2:
	usage()

dirname = sys.argv[1]

print("progname,its,its ext,ia,gd,flips,arithms,int,havoc,multigoal,sis,tot")
for file in sorted(list(iterate_files(dirname))):
	if "flips" not in os.path.basename(file):
		continue

	progname = os.path.basename(file).split("-")[0]
	print(progname, end=",")
	with open(file, "r") as fin:
		vals = fin.readline().split(",")
		print(",".join(vals), end=",")
		print(reduce(lambda x, y: x+y, map(int, vals)))
