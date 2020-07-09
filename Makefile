CC=gcc #clang
CFLAGS=-Wall -s -O3 -fPIC #-O3 -g -fsanitize=address -fno-omit-frame-pointer -fPIC
CLIBS=-lz3
CLIB_PATHS=-L./fuzzolic-z3/build
CINCLUDE=-I./fuzzolic-z3/src/api -I./include

all: solver fuzzy-solver fuzzy-solver-notify fuzzy-solver-vs-z3 eval-driver maxmin-driver debug-eval findall-driver

fuzzy-solver: fuzzy-lib
	${CC} ${CFLAGS} fuzzy-solver.c ./utility/pretty-print.c libZ3Fuzzy.a -o fuzzy-solver ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

fuzzy-solver-notify: fuzzy-lib
	${CC} ${CFLAGS} fuzzy-solver-notify.c ./utility/pretty-print.c libZ3Fuzzy.a -o fuzzy-solver-notify ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

fuzzy-solver-vs-z3: fuzzy-lib
	${CC} ${CFLAGS} fuzzy-solver-vs-z3.c ./utility/pretty-print.c libZ3Fuzzy.a -o fuzzy-solver-vs-z3 ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

solver:
	${CC} ${CFLAGS} solver.c ./utility/pretty-print.c -o solver ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

eval-driver: fuzzy-lib
	${CC} ${CFLAGS} eval-driver.c ./utility/pretty-print.c libZ3Fuzzy.a -o eval-driver ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

maxmin-driver: fuzzy-lib
	${CC} ${CFLAGS} maxmin-driver.c ./utility/pretty-print.c libZ3Fuzzy.a -o maxmin-driver ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

findall-driver: fuzzy-lib
	${CC} ${CFLAGS} findall-driver.c libZ3Fuzzy.a -o findall-driver ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

debug-eval: fuzzy-lib
	${CC} ${CFLAGS} debug-eval.c ./utility/pretty-print.c libZ3Fuzzy.a -o debug-eval ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

fuzzy-lib:
	${CC} ${CFLAGS} -c z3-fuzzy.c ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}
	${CC} ${CFLAGS} -c ./utility/md5.c ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}
	${CC} ${CFLAGS} -c ./utility/gradient_descend.c ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}
	${CC} ${CFLAGS} -c ./utility/wrapped_interval.c ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}
	${CC} ${CFLAGS} -c ./utility/timer.c ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}
	${CC} ${CFLAGS} -c testcase-list.c ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}
	ar rcs libZ3Fuzzy.a z3-fuzzy.o testcase-list.o gradient_descend.o md5.o wrapped_interval.o timer.o
	rm z3-fuzzy.o testcase-list.o gradient_descend.o md5.o wrapped_interval.o timer.o

interval-test:
	${CC} ${CFLAGS} interval_test.c ./utility/wrapped_interval.c -o interval_test

clean:
	rm -f libZ3Fuzzy.a fuzzy-solver fuzzy-solver-notify solver eval-driver maxmin-driver debug-eval findall-driver

clean-tests:
	rm tests/*
