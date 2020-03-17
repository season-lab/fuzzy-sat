#!/usr/bin/env python3

import z3
import sys

ctx = z3.Context()
s = z3.Solver(ctx=ctx)
queries_1 = z3.parse_smt2_file(sys.argv[1])
queries_2 = z3.parse_smt2_file(sys.argv[2])

queries_1 = set(queries_1)
queries_2 = set(queries_2)

diff = queries_1 - queries_2
import IPython; IPython.embed()
for query in diff:
  print("(assert\n" + query.sexpr() + "\n)")
