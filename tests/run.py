#!/usr/bin/env python3

import subprocess
import pytest
import os

SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))
FUZZY_BIN  = os.path.join(SCRIPT_DIR, "../build/bin/fuzzy-solver")
if "FUZZY_BIN" in os.environ:
    FUZZY_BIN = os.environ["FUZZY_BIN"]

ZERO_SEED = os.path.join(SCRIPT_DIR, "zero_seed.bin")

def get_path(query):
    return os.path.join(SCRIPT_DIR, query)

def common(query, seed):
    cmd = [FUZZY_BIN, "--notui", "-q", query, "-s", seed]
    out = subprocess.check_output(cmd)
    return b"SAT" in out

def test_its_000():
    assert common(get_path("001_its.smt2"), ZERO_SEED)

def test_arithm_000():
    assert common(get_path("002_arithm.smt2"), ZERO_SEED)

def test_arithm_001():
    assert common(get_path("003_arithm.smt2"), ZERO_SEED)

def test_arithm_002():
    assert common(get_path("004_arithm.smt2"), ZERO_SEED)

def test_arithm_003():
    assert common(get_path("005_arithm.smt2"), ZERO_SEED)
