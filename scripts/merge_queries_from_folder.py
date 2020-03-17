#!/usr/bin/env python3

import z3
import re
import os
import sys

def find_inputs(query):
    inputs = re.findall(r"k![0-9]+", query.sexpr().replace("\n", ""))
    return set(inputs)

if len(sys.argv) < 3:
    print("USAGE: %s directory smt_file" % sys.argv[0])
    exit(1)

directory = sys.argv[1]
smt_file  = sys.argv[2]

if not os.path.exists(directory):
    print("ERROR: %s does not exist" % directory)
    exit(1)

inputs = set()
res = ""
for filename in os.listdir(directory):
    filename = directory + "/" + filename
    if filename.endswith(".smt2"):
        print(filename)
        queries = z3.parse_smt2_file(filename)
        for query in queries:
            res += "(assert \n" + query.sexpr() + "\n)\n"
            inputs |= find_inputs(query)

fout = open(smt_file, "w")
for inp in inputs:
    fout.write("(declare-const %s (_ BitVec 8))\n" % inp)
fout.write(res)
fout.close()
