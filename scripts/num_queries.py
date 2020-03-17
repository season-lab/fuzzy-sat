
import z3
import sys

ctx = z3.Context()
s = z3.Solver(ctx=ctx)
queries = z3.parse_smt2_file(sys.argv[1])

print("num queries:", len(queries))
