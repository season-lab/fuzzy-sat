#!/bin/bash

#!/bin/bash

SCRIPTPATH="$( cd "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"
BIN_FUZZY=$SCRIPTPATH/../fuzzy-solver-notify
QUERIES_PATH=$SCRIPTPATH/../query_db/without_models
SEED_PATH=$SCRIPTPATH/../query_db/seeds

export LD_LIBRARY_PATH=$SCRIPTPATH/../fuzzolic-z3/build

function execute_bench {
    query_path=$1
    seed_path=$2
    exp_name=$3
    out_file=$4

    echo "running exp $exp_name on fuzzy..."
    output=$($BIN_FUZZY $query_path $seed_path)
    tot_time=$(echo "$output" | grep "elaps time + par" | cut -d':' -f2 | sed 's/s//g' | sed 's/ //g')
    time_par=$(echo "$output" | grep "elaps par" | cut -d':' -f2 | sed 's/s//g' | sed 's/ //g')

    echo "$exp_name,$time_par,$tot_time" >> $out_file
    echo "DONE"
}

function execute_run {
    out_dir=$1
    run_n=$2

    out_file=$out_dir/fuzzy-times-with-parsing-$run_n.csv

    execute_bench $QUERIES_PATH/advmng.smt2              $SEED_PATH/mappy.mng          advmng   $out_file
    execute_bench $QUERIES_PATH/advzip.smt2              $SEED_PATH/small_archive.zip  advzip   $out_file
    execute_bench $QUERIES_PATH/bloaty.smt2              $SEED_PATH/small_exec.elf     bloaty   $out_file
    execute_bench $QUERIES_PATH/bsdtar.smt2              $SEED_PATH/tar.tar            bsdtar   $out_file
    execute_bench $QUERIES_PATH/djpeg.smt2               $SEED_PATH/not_kitty.jpg      djpeg    $out_file
    execute_bench $QUERIES_PATH/jhead.smt2               $SEED_PATH/not_kitty.jpg      jhead    $out_file
    execute_bench $QUERIES_PATH/libpng.smt2              $SEED_PATH/not_kitty.png      libpng   $out_file
    execute_bench $QUERIES_PATH/lodepng_decode_nock.smt2 $SEED_PATH/not_kitty.png      lodepng  $out_file
    execute_bench $QUERIES_PATH/optipng.smt2             $SEED_PATH/not_kitty.png      optipng  $out_file
    execute_bench $QUERIES_PATH/readelf.smt2             $SEED_PATH/small_exec.elf     readelf  $out_file
    execute_bench $QUERIES_PATH/tcpdump.smt2             $SEED_PATH/small_capture.pcap tcpdump  $out_file
    execute_bench $QUERIES_PATH/tiff2pdf.smt2            $SEED_PATH/not_kitty.tiff     tiff2pdf $out_file
    execute_bench $QUERIES_PATH/objdump.smt2             $SEED_PATH/small_exec.elf     objdump  $out_file
}

OUT_DIR=$SCRIPTPATH/../exp_logs/exp-nuovi/fuzzy-times-with-parsing

execute_run $OUT_DIR 1
execute_run $OUT_DIR 2
execute_run $OUT_DIR 3
