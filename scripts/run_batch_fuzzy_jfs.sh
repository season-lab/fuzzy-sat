#!/bin/bash

SCRIPTPATH="$( cd "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"
QUERIES_PATH=$SCRIPTPATH/../query_db/single_queries
SEED_PATH=$SCRIPTPATH/../query_db/seeds

export LD_LIBRARY_PATH=$SCRIPTPATH/../fuzzolic-z3/build

function execute_bench {
    queries_dir=$1
    seed_path=$2
    exp_name=$3
    out_dir=$4

    echo "running exp $exp_name on fuzzy..."
    $SCRIPTPATH/run_on_multiple_queries.py \
        $queries_dir $seed_path $out_dir/$exp_name-fuzzy.csv fuzzy

    echo "running exp $exp_name on jfs..."
    docker run --rm \
        -v $out_dir:/home/user/out \
        -v $queries_dir:/home/user/queries:ro \
        -v $SCRIPTPATH/run_on_multiple_queries.py:/home/user/run_on_multiple_queries.py:ro \
        delcypher/jfs_build:fse_2019 \
        /home/user/run_on_multiple_queries.py \
            /home/user/queries 0 /home/user/out/$exp_name-jfs.csv jfs

    echo "DONE"
}

function execute_run {
    out_dir=$1
    run_n=$2

    out_dir=$out_dir/run-$run_n

    [ -d $out_dir ] && echo "Directory $out_dir exists." && exit 1

    mkdir $out_dir

    tar xzf $QUERIES_PATH/advmng_queries.tar.gz -C /tmp
    execute_bench /tmp/advmng_queries $SEED_PATH/mappy.mng advmng $out_dir
    rm -rf /tmp/advmng_queries

    tar xzf $QUERIES_PATH/advzip_queries.tar.gz -C /tmp
    execute_bench /tmp/advzip_queries $SEED_PATH/small_archive.zip advzip $out_dir
    rm -rf /tmp/advzip_queries

    tar xzf $QUERIES_PATH/bloaty_queries.tar.gz -C /tmp
    execute_bench /tmp/bloaty_queries $SEED_PATH/small_exec.elf bloaty $out_dir
    rm -rf /tmp/bloaty_queries

    tar xzf $QUERIES_PATH/bsdtar_queries.tar.gz -C /tmp
    execute_bench /tmp/bsdtar_queries $SEED_PATH/tar.tar bsdtar $out_dir
    rm -rf /tmp/bsdtar_queries

    tar xzf $QUERIES_PATH/djpeg_queries.tar.gz -C /tmp
    execute_bench /tmp/djpeg_queries $SEED_PATH/not_kitty.jpg djpeg $out_dir
    rm -rf /tmp/djpeg_queries

    tar xzf $QUERIES_PATH/jhead_queries.tar.gz -C /tmp
    execute_bench /tmp/jhead_queries $SEED_PATH/not_kitty.jpg jhead $out_dir
    rm -rf /tmp/jhead_queries

    tar xzf $QUERIES_PATH/libpng_queries.tar.gz -C /tmp
    execute_bench /tmp/libpng_queries $SEED_PATH/not_kitty.png libpng $out_dir
    rm -rf /tmp/libpng_queries

    tar xzf $QUERIES_PATH/lodepng_queries.tar.gz -C /tmp
    execute_bench /tmp/lodepng_queries $SEED_PATH/not_kitty.png lodepng $out_dir
    rm -rf /tmp/lodepng_queries

    tar xzf $QUERIES_PATH/optipng_queries.tar.gz -C /tmp
    execute_bench /tmp/optipng_queries $SEED_PATH/not_kitty.png optipng $out_dir
    rm -rf /tmp/optipng_queries

    tar xzf $QUERIES_PATH/readelf_queries.tar.gz -C /tmp
    execute_bench /tmp/readelf_queries $SEED_PATH/small_exec.elf readelf $out_dir
    rm -rf /tmp/readelf_queries

    tar xzf $QUERIES_PATH/tcpdump_queries.tar.gz -C /tmp
    execute_bench /tmp/tcpdump_queries $SEED_PATH/small_capture.pcap tcpdump $out_dir
    rm -rf /tmp/tcpdump_queries

    tar xzf $QUERIES_PATH/tiff2pdf_queries.tar.gz -C /tmp
    execute_bench /tmp/tiff2pdf_queries $SEED_PATH/not_kitty.tiff tiff2pdf $out_dir
    rm -rf /tmp/tiff2pdf_queries

    tar xzf $QUERIES_PATH/objdump_queries.tar.gz -C /tmp
    execute_bench /tmp/objdump_queries $SEED_PATH/small_exec.elf objdump $out_dir
    rm -rf /tmp/objdump_queries
}

OUT_DIR=$SCRIPTPATH/../exp_logs/exp-nuovi/fuzzy-jsf

execute_run $OUT_DIR 1
execute_run $OUT_DIR 2
execute_run $OUT_DIR 3
