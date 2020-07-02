#!/bin/bash

echo 0 | sudo tee /proc/sys/kernel/yama/ptrace_scope > /dev/null
export LD_LIBRARY_PATH=../fuzzolic-z3/build

HOST_BENCH=/home/luca/Documents/git/exp-docker/host_bin/benchmarks
GUEST_BENCH=/home/qsym/benchmarks

function run_exp {
	seed_file=$1
	prog_name=$2
	args=$3

	rm -rf /dev/shm/*
	echo ""
	echo "> exp $prog_name <"
	echo ""
	echo "[+] running docker..."
	docker run --rm						\
		-v /dev/shm:/mnt/out			\
		-v $HOST_BENCH:$GUEST_BENCH		\
		qsym-fuzzy-exp 					\
			 /bin/bash -c 				\
			 	"source ./fuzzers/qsym-fuzzy/venv/bin/activate &&					\
				./fuzzers/qsym-fuzzy/bin/run_qsym.py 								\
					-i $GUEST_BENCH/$seed_file -o /mnt/out -- $GUEST_BENCH/$args"

	mv /dev/shm/qsym-out-0/querylog.log ../query_db/exp_out/$prog_name
	echo "[+] fixing query...."
	./fix_query.sh ../query_db/exp_out/$prog_name
	mv ../query_db/exp_out/$prog_name.FIXED.smt2 ../query_db/exp_out/$prog_name.smt2
	rm ../query_db/exp_out/$prog_name
	echo "[+] running fuzzy-solver vs z3..."
	../fuzzy-solver-vs-z3 ../query_db/exp_out/$prog_name.smt2 $HOST_BENCH/$seed_file
	mv ./fuzzy_z3.csv ../query_db/exp_out/$prog_name.csv
	echo "[+] done"
	rm -rf /dev/shm/*
}

# run_exp tcpdump/seeds/small_capture.pcap tcpdump "tcpdump/tcpdump_nopie -e -vv -nr @@"
# run_exp bloaty/seeds/small_exec.elf bloaty "bloaty/bloaty @@"
# run_exp djpeg/seeds/not_kitty.jpg djpeg "djpeg/djpeg @@"
# run_exp readelf/seeds/small_exec.elf readelf "readelf/readelf_nopie -a @@"
# run_exp jhead/seeds/not_kitty.jpg jhead "jhead/jhead @@"
# run_exp tiff2pdf/seeds/not_kitty.tiff tiff2pdf "tiff2pdf/tiff2pdf_nopie @@"
# run_exp advmng/seeds/mappy.mng advmng "advmng/advmng -l @@"
# run_exp advzip/seeds/small_archive.zip advzip "advzip/advzip -l @@"
# run_exp gocr/seeds/not_kitty.png gocr "gocr/gocr @@"
# run_exp optipng/seeds/not_kitty.png optipng "optipng/optipng -out /dev/null @@"
