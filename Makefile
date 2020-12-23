CC=gcc #clang
CFLAGS=-Wall -s -O3 -fPIC #-O3 -g -fsanitize=address -fno-omit-frame-pointer -fPIC
CLIBS=-lz3
CLIB_PATHS=-L./fuzzolic-z3/build
CINCLUDE=-I./fuzzolic-z3/src/api -I./lib

SRC_LIB_DIR=./lib
SRC_TOOLS_DIR=./tools
BIN_DIR=./build/bin
LIB_DIR=./build/lib
INC_DIR=./build/include

all: fuzzy-solver-notify fuzzy-solver-vs-z3 stats-collection-z3 stats-collection-fuzzy

fuzzy-solver-notify: fuzzy-lib
	${CC} ${CFLAGS} ${SRC_TOOLS_DIR}/fuzzy-solver-notify.c ${SRC_TOOLS_DIR}/pretty-print.c ${LIB_DIR}/libZ3Fuzzy.a -o ${BIN_DIR}/fuzzy-solver ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

fuzzy-solver-vs-z3: fuzzy-lib
	${CC} ${CFLAGS} ${SRC_TOOLS_DIR}/fuzzy-solver-vs-z3.c ${SRC_TOOLS_DIR}/pretty-print.c ${LIB_DIR}/libZ3Fuzzy.a -o ${BIN_DIR}/fuzzy-solver-vs-z3 ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

stats-collection-z3:
	${CC} ${CFLAGS} ${SRC_TOOLS_DIR}/stats-collection-z3.c ${SRC_TOOLS_DIR}/pretty-print.c -o ${BIN_DIR}/stats-collection-z3 ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

stats-collection-fuzzy: fuzzy-lib
	${CC} ${CFLAGS} ${SRC_TOOLS_DIR}/stats-collection-fuzzy.c ${SRC_TOOLS_DIR}/pretty-print.c ${LIB_DIR}/libZ3Fuzzy.a -o ${BIN_DIR}/stats-collection-fuzzy ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

eval-driver: fuzzy-lib
	${CC} ${CFLAGS} ${SRC_TOOLS_DIR}/eval-driver.c ${SRC_TOOLS_DIR}/pretty-print.c ${LIB_DIR}/libZ3Fuzzy.a -o ${BIN_DIR}/eval-driver ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

maxmin-driver: fuzzy-lib
	${CC} ${CFLAGS} ${SRC_TOOLS_DIR}/maxmin-driver.c ${SRC_TOOLS_DIR}/pretty-print.c ${LIB_DIR}/libZ3Fuzzy.a -o ${BIN_DIR}/maxmin-driver ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

findall-driver: fuzzy-lib
	${CC} ${CFLAGS} ${SRC_TOOLS_DIR}/findall-driver.c ${LIB_DIR}/libZ3Fuzzy.a -o ${BIN_DIR}/findall-driver ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

debug-eval: fuzzy-lib
	${CC} ${CFLAGS} ${SRC_TOOLS_DIR}/debug-eval.c ${SRC_TOOLS_DIR}/pretty-print.c ${LIB_DIR}/libZ3Fuzzy.a -o ${BIN_DIR}/debug-eval ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}

fuzzy-lib:
	${CC} ${CFLAGS} -c ${SRC_LIB_DIR}/z3-fuzzy.c ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}
	${CC} ${CFLAGS} -c ${SRC_LIB_DIR}/md5.c ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}
	${CC} ${CFLAGS} -c ${SRC_LIB_DIR}/gradient_descend.c ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}
	${CC} ${CFLAGS} -c ${SRC_LIB_DIR}/wrapped_interval.c ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}
	${CC} ${CFLAGS} -c ${SRC_LIB_DIR}/timer.c ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}
	${CC} ${CFLAGS} -c ${SRC_LIB_DIR}/testcase-list.c ${CINCLUDE} ${CLIB_PATHS} ${CLIBS}
	ar rcs ${LIB_DIR}/libZ3Fuzzy.a z3-fuzzy.o testcase-list.o gradient_descend.o md5.o wrapped_interval.o timer.o
	cp ${SRC_LIB_DIR}/z3-fuzzy.h ${INC_DIR}/z3-fuzzy.h
	rm z3-fuzzy.o testcase-list.o gradient_descend.o md5.o wrapped_interval.o timer.o

interval-test:
	${CC} ${CFLAGS} interval_test.c ./lib/wrapped_interval.c -o interval_test

clean:
	rm -f ${BIN_DIR}/fuzzy-solver ${BIN_DIR}/fuzzy-solver-vs-z3 ${LIB_DIR}/libZ3Fuzzy.a ${INC_DIR}/z3-fuzzy.h

clean-tests:
	rm tests/*
