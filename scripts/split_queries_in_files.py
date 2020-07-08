#!/usr/bin/env python3

import z3
import re
import os
import sys

if len(sys.argv) < 3:
    print("USAGE: %s smt2_file directory", sys.argv[0])
    exit(1)

def deduplicate_query(query):
    if query.decl().kind() == z3.Z3_OP_AND:
        branch_condition = query.children()[0]  # preserve branch condition
                                                # first position
        other_asserts = query.children()[1:]
        return z3.And(*([branch_condition] + list(set(other_asserts))))
    return query

def find_inputs(query):
    inputs = re.findall(r"k![0-9]+", query.sexpr().replace("\n", ""))
    return set(inputs)

def find_addresses(filename):
    fin = open(filename, "r")
    addresses = []
    for line in fin:
        if line.startswith("; ADDRESS "):
            address = int(line.strip().split(" ")[2], 16)
            addresses.append(address)
    fin.close()
    return addresses

smt_file  = sys.argv[1]
directory = sys.argv[2]

queries = z3.parse_smt2_file(smt_file)
addresses = find_addresses(smt_file)
has_address = len(addresses) > 0

if not has_address:
    print("WARNING: no addresses")
else:
    assert len(addresses) == len(queries)

if not os.path.exists(directory):
    os.mkdir(directory)

i = 0
for query in queries:
    # query = deduplicate_query(query)
    filename = "query_%03d_@_0x%x.smt2" % (i, addresses[i] if has_address else 0)
    fout = open(directory + "/" + filename, "w")
    for inp in find_inputs(query):
        fout.write("(declare-const %s (_ BitVec 8))\n" % inp)
    fout.write("(assert \n" + query.sexpr() + "\n)\n(check-sat)")
    fout.close()
    i += 1
