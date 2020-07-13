#!/usr/bin/env python3

import subprocess
import time
import sys
import os

SCRIPT_PATH = os.path.dirname(os.path.realpath(__file__))

def usage():
    print("%s <queries-dir> <seed> <logfile>" % sys.argv[0])
    exit(1)

def iterate_files(path):
    for subdir, _, files in os.walk(path):
        for file in files:
            yield os.path.join(subdir, file)
        break

def docker_check_kill(docker_name):
    s = subprocess.check_output(["docker", "ps"])
    if docker_name in s.decode("ascii", errors="ignore"):
        subprocess.check_call(
            ["docker", "kill", docker_name],
            stderr=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL)

def run_fuzzy(query, seed):
    start = time.time()
    try:
        output = subprocess.check_output(
            [os.path.join(SCRIPT_PATH, "../fuzzy-solver-notify"), query, seed],
            timeout=2,
            stderr=subprocess.DEVNULL,
            env={"LD_LIBRARY_PATH": os.path.join(SCRIPT_PATH, "../fuzzolic-z3/build")}
        )
    except subprocess.TimeoutExpired:
        output = b""
    end = time.time()
    elapsed = (end - start) * 1000.0

    if b"fast sat queries: 1" in output:
        return True, elapsed
    return False, elapsed

def run_jfs_docker(query):
    start = time.time()
    try:
        output = subprocess.check_output(
            [
                "docker", "run", "--user", "1000", "--rm", "-v",
                "%s:/tmp/q.smt2" % os.path.realpath(query), 
                "--name", "jfs-runner", "-t", "delcypher/jfs_build:fse_2019", 
                "/home/user/jfs/build/bin/jfs", "-max-time=1", "/tmp/q.smt2"
            ],
            timeout=2,
            stderr=subprocess.DEVNULL,
        )
    except subprocess.TimeoutExpired:
        output = b""
    end = time.time()
    elapsed = (end - start) * 1000.0

    docker_check_kill("jfs-runner")

    if b"sat" in output and b"unsat" not in output:
        return True, elapsed
    return False, elapsed

def run_jfs(query):
    start = time.time()
    try:
        output = subprocess.check_output(
            [
                "/home/user/jfs/build/bin/jfs", "-max-time=1", query
            ],
            timeout=2,
            stderr=subprocess.DEVNULL,
        )
    except subprocess.TimeoutExpired:
        output = b""
    end = time.time()
    elapsed = (end - start) * 1000.0

    if b"sat" in output and b"unsat" not in output:
        return True, elapsed
    return False, elapsed

def exp_jfs(queries_dir, logfile):
    f = open(logfile, "w")
    for query in sorted(list(iterate_files(queries_dir))):
        sat_jfs, time_jfs = run_jfs(query)
        f.write("%d,%.03f\n" % (1 if sat_jfs else 0, time_jfs))

    f.close()

def exp_fuzzy(queries_dir, seed, logfile):
    f = open(logfile, "w")
    for query in sorted(list(iterate_files(queries_dir))):
        sat_fuzzy, time_fuzzy = run_fuzzy(query, seed)
        f.write("%d,%.03f\n" % (1 if sat_fuzzy else 0, time_fuzzy))

    f.close()

if len(sys.argv) < 4:
    usage()

queries_dir = sys.argv[1]
seed        = sys.argv[2]
logfile     = sys.argv[3]

# exp_jfs(queries_dir, logfile)
exp_fuzzy(queries_dir, seed, logfile)
