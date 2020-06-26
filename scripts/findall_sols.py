#!/usr/bin/env python3

import sys
import z3

def usage():
  print("%s <query.smt2> <id1> [<id2> ... <idn>]" % sys.argv[0])
  exit(1)

if len(sys.argv) < 3:
  usage()

query_f = sys.argv[1]
ids     = list(map(int, sys.argv[2:]))

query = z3.parse_smt2_file(query_f)

bvs = [z3.BitVec("k!%d" % i, 8) for i in ids]
bv  = bvs[0]
for i in range(1, len(bvs)):
  bv = z3.Concat(bvs[i], bv)

s = z3.Solver()
s.add(query)

import IPython; IPython.embed()

j = 1
while s.check().r == 1:
  m = s.model()
  v = m.eval(bv)
  v = v.as_long()

  print("SOL %d" % j)
  for i in range(len(ids)):
    k_v = (v >> i*8) & 0xff
    print("  k!%03d: 0x%02x" % (ids[i], k_v))

  s.add(bv != v)
  print()

  j += 1