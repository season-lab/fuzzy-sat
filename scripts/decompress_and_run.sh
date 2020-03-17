#!/bin/bash

solver=$1
query_compressed_file=$2
seed_file=$3

tar -xzf $query_compressed_file -C /tmp

$solver /tmp/query.smt2 $seed_file

rm /tmp/query.smt2
