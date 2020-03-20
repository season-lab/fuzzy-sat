#!/usr/bin/env python3

import z3
import sys

ctx = z3.Context()
s = z3.Solver(ctx=ctx)
queries = z3.parse_smt2_file(sys.argv[1])
k = int(sys.argv[2])
outfile = sys.argv[3]

query = queries[k]

with open(outfile, "w") as fout:
    fout.write("(assert\n" + query.sexpr() + "\n)\n")
