CC=gcc
CFLAGS=-Wall -g -O3
CLIBS=-lz3
CLIB_PATHS=-L./fuzzolic-z3/build
CINCLUDE=-I./fuzzolic-z3/src/api -I./include

all: solver fuzzy-solver eval-driver maxmin-driver debug-eval

fuzzy-solver: fuzzy-lib
	${CC} ${CFLAGS} fuzzy-solver.c ./utility/*.c z3-fuzzy-lib.a -o fuzzy-solver ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

solver:
	${CC} ${CFLAGS} solver.c ./utility/*.c -o solver ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

eval-driver: fuzzy-lib
	${CC} ${CFLAGS} eval-driver.c ./utility/*.c z3-fuzzy-lib.a -o eval-driver ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

maxmin-driver: fuzzy-lib
	${CC} ${CFLAGS} maxmin-driver.c ./utility/*.c z3-fuzzy-lib.a -o maxmin-driver ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

debug-eval: fuzzy-lib
	${CC} ${CFLAGS} debug-eval.c ./utility/*.c z3-fuzzy-lib.a -o debug-eval ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

fuzzy-lib:
	sed -i 's/Z3_VERSION [0-9]\+/Z3_VERSION 487/g' z3-fuzzy.h
	${CC} ${CFLAGS} -c z3-fuzzy.c ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}
	${CC} ${CFLAGS} -c testcase-list.c ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}
	ar rcs z3-fuzzy-lib.a z3-fuzzy.o testcase-list.o
	rm z3-fuzzy.o testcase-list.o

clean:
	rm -f z3-fuzzy-lib.a z3-fuzzy-lib-old.a fuzzy-solver solver test-old

clean-tests:
	rm tests/*
