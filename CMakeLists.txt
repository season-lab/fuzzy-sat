cmake_minimum_required(VERSION 3.7)

project(Z3Fuzzy)

set(Z3_BUILD_PYTHON_BINDINGS true)
add_subdirectory(fuzzolic-z3)
add_subdirectory(lib)
add_subdirectory(tools)
