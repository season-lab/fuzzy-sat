cmake_minimum_required(VERSION 3.7)

# Strip the binary in release mode
set(CMAKE_C_FLAGS_RELEASE "${CMAKE_C_FLAGS_RELEASE} -s")

set(z3fuzzy_src
                z3-fuzzy.c
                md5.c
                gradient_descend.c
                wrapped_interval.c
                timer.c
                testcase-list.c )

add_library(objZ3FuzzyLib OBJECT ${z3fuzzy_src})

set_property(TARGET objZ3FuzzyLib PROPERTY POSITION_INDEPENDENT_CODE 1)

add_library(Z3Fuzzy_static STATIC $<TARGET_OBJECTS:objZ3FuzzyLib>)
add_library(Z3Fuzzy_shared SHARED $<TARGET_OBJECTS:objZ3FuzzyLib>)

target_include_directories (objZ3FuzzyLib PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/../fuzzolic-z3/src/api")
target_link_libraries (Z3Fuzzy_shared LINK_PUBLIC libz3)

set_target_properties(Z3Fuzzy_static PROPERTIES OUTPUT_NAME Z3Fuzzy)
set_target_properties(Z3Fuzzy_shared PROPERTIES OUTPUT_NAME Z3Fuzzy)

install(FILES z3-fuzzy.h DESTINATION include)
