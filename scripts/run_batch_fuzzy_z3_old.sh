#!/bin/bash

SCRIPTPATH="$( cd "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"
BIN=$SCRIPTPATH/../fuzzy-solver-vs-z3
QUERIES_PATH=$SCRIPTPATH/../query_db/without_models
SEED_PATH=$SCRIPTPATH/../query_db/seeds

export LD_LIBRARY_PATH=$SCRIPTPATH/../fuzzolic-z3/build

function execute_bench {
    query_path=$1
    seed_path=$2
    exp_name=$3
    out_dir=$4

    echo "running exp $exp_name..."
    $BIN $query_path $seed_path

    mv ./fuzzy_z3.csv $out_dir/$exp_name-queries.csv
    mv ./fuzzy_flip_info.csv $out_dir/$exp_name-flips.csv
    echo "DONE"
}

OUT_DIR=$SCRIPTPATH/../exp_logs/fuzzy_z3_10sec

# execute_bench $QUERIES_PATH/advmng.smt2              $SEED_PATH/mappy.mng          advmng   $OUT_DIR
# execute_bench $QUERIES_PATH/advzip.smt2              $SEED_PATH/small_archive.zip  advzip   $OUT_DIR
# execute_bench $QUERIES_PATH/bloaty.smt2              $SEED_PATH/small_exec.elf     bloaty   $OUT_DIR
# execute_bench $QUERIES_PATH/djpeg.smt2               $SEED_PATH/not_kitty.jpg      djpeg    $OUT_DIR
# execute_bench $QUERIES_PATH/jhead.smt2               $SEED_PATH/not_kitty.jpg      jhead    $OUT_DIR
# execute_bench $QUERIES_PATH/libpng.smt2              $SEED_PATH/not_kitty.png      libpng   $OUT_DIR
# execute_bench $QUERIES_PATH/lodepng_decode_nock.smt2 $SEED_PATH/not_kitty.png      lodepng  $OUT_DIR
# execute_bench $QUERIES_PATH/optipng.smt2             $SEED_PATH/not_kitty.png      optipng  $OUT_DIR
# execute_bench $QUERIES_PATH/readelf.smt2             $SEED_PATH/small_exec.elf     readelf  $OUT_DIR
# execute_bench $QUERIES_PATH/tcpdump.smt2             $SEED_PATH/small_capture.pcap tcpdump  $OUT_DIR
# execute_bench $QUERIES_PATH/tiff2pdf.smt2            $SEED_PATH/not_kitty.tiff     tiff2pdf $OUT_DIR
execute_bench $QUERIES_PATH/objdump.smt2             $SEED_PATH/small_exec.elf     objdump  $OUT_DIR
