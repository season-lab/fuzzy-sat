cmake_minimum_required(VERSION 3.7)

macro(LinkBin exe_name)
    target_link_libraries(${exe_name} LINK_PUBLIC libz3)
    target_link_libraries(${exe_name} LINK_PUBLIC Z3Fuzzy_static)
    target_include_directories(${exe_name} PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/../fuzzolic-z3/src/api")
    target_include_directories(${exe_name} PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/../lib")
endmacro()

add_executable(fuzzy-solver
    fuzzy-solver-notify.c
    pretty-print.c)
LinkBin(fuzzy-solver)

add_executable(fuzzy-solver-vs-z3
    fuzzy-solver-vs-z3.c
    pretty-print.c)
LinkBin(fuzzy-solver-vs-z3)

add_executable(stats-collection-fuzzy
    stats-collection-fuzzy.c
    pretty-print.c)
LinkBin(stats-collection-fuzzy)

add_executable(stats-collection-z3
    stats-collection-z3.c
    pretty-print.c)
LinkBin(stats-collection-z3)
