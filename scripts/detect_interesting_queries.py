#!/usr/bin/env python3

import subprocess
import sys
import os 

dir_path = os.path.dirname(os.path.realpath(__file__))

fuzzy_solver_path = dir_path + "/../fuzzy-solver"
z3_solver_path    = dir_path + "/../solver"

if len(sys.argv) < 3:
    print("USAGE: %s queries_dir seed_path" % sys.argv[0])
    exit(1)

directory = sys.argv[1]
seed = sys.argv[2]

devnull = open(os.devnull, 'w')

for filename in os.listdir(directory):
    if filename.endswith(".smt2"):
        filepath = directory + "/" + filename
        fuzzy_out = subprocess.check_output([fuzzy_solver_path, filepath, seed], stderr=devnull)
        solver_out = subprocess.check_output([z3_solver_path, filepath], stderr=devnull)

        fuzzy_sat = int(list(filter(lambda x: b"fast sat" in x, fuzzy_out.split(b"\n")))[0].split(b"\t")[1])
        solver_sat = int(list(filter(lambda x: b"sat queries" in x, solver_out.split(b"\n")))[0].split(b"\t")[1])
        solver_unk = int(list(filter(lambda x: b"unkn queries" in x, solver_out.split(b"\n")))[0].split(b"\t")[1])
        
        if fuzzy_sat == 1 and solver_unk == 1:
            print(filename, "is interesting! (fuzzy ok, solver unknown)")
        if fuzzy_sat == 0 and solver_sat == 1:
            print(filename, "is interesting! (fuzzy fail, solver ok)")

devnull.close()
