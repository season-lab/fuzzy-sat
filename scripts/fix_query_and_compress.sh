#!/bin/bash

SCRIPTPATH="$( cd "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"

query_file=$1
query_name=`basename $query_file`

max_inp=`grep -o "k\![0-9]*" $query_file | cut -d'!' -f2 | sort -n | tail -n 1`
max_inp=`echo "$max_inp" | sed 's/\ *//g'`

echo -n "" > /tmp/query.smt2
for i in `seq 0 $max_inp`; do
    echo "(declare-const k!$i (_ BitVec 8))" >> /tmp/query.smt2
done
cat $query_file >> /tmp/query.smt2

pushd /tmp > /dev/null
tar -czf $SCRIPTPATH/../query_db/$query_name.tar.gz query.smt2
popd > /dev/null

rm /tmp/query.smt2
