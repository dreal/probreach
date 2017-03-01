cmake_minimum_required(VERSION 2.6)
# project name
project(ProbReach)

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${PROJECT_SOURCE_DIR}/cmake/Modules/")

# checking for packages
find_package(DREAL REQUIRED)
find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)
find_package(GSL REQUIRED)
find_package(GTest)

# setting compiler flags
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3 -Wall -Wno-sign-compare -Wno-unused-variable -Wno-return-type -Wno-unused-function -std=c++11 -fopenmp -frounding-math")
set(CMAKE_EXE_LINKER_FLAGS "-static-libgcc -static-libstdc++")

# setting some environment variables
set(PROBREACH_SOURCE_DIR ${CMAKE_SOURCE_DIR}/src)
set(PROBREACH_BINARY_DIR ${CMAKE_BINARY_DIR})
set(PROBREACH_TEST_DIR ${CMAKE_SOURCE_DIR}/test)

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})

# setting ProbReach version
set(PROBREACH_VERSION_MAJOR 1)
set(PROBREACH_VERSION_MINOR 4)

# getting git commit as a string
include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)
configure_file(
        "${PROBREACH_SOURCE_DIR}/util/git_sha1.cpp.in"
        "${PROBREACH_BINARY_DIR}/git_sha1.cpp" @ONLY)

set(PROBREACH_VERSION ${PROBREACH_VERSION_MAJOR}.${PROBREACH_VERSION_MINOR})
configure_file(
        "${PROBREACH_SOURCE_DIR}/version.h.in"
        "${PROBREACH_SOURCE_DIR}/version.h"
)

configure_file(
        "${PROBREACH_SOURCE_DIR}/config.h.in"
        "${PROBREACH_SOURCE_DIR}/config.h"
)

# creating a directory for the lexer and parser files
add_custom_target(pdrhparser
        COMMAND ${CMAKE_COMMAND} -E make_directory ${PROBREACH_BINARY_DIR}/parser/pdrh
        COMMENT "Creating directory ${PROBREACH_BINARY_DIR}/parser/pdrh")

# create custom command for flex/lex (note the outputs)
add_custom_command(
        COMMAND ${FLEX_EXECUTABLE}
        ARGS -o ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
        ${PROBREACH_SOURCE_DIR}/parser/pdrh/pdrhlexer.l
        DEPENDS pdrhparser
        DEPENDS ${PROBREACH_SOURCE_DIR}/parser/pdrh/pdrhlexer.l
        OUTPUT  ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
        COMMENT "Generating ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c"
)

# create custom command for bison/yacc (note the DEPENDS)
add_custom_command(
        COMMAND ${BISON_EXECUTABLE}
        ARGS -d -y ${PROBREACH_SOURCE_DIR}/parser/pdrh/pdrhparser.y
        -o ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
        DEPENDS ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
        DEPENDS ${PROBREACH_SOURCE_DIR}/parser/pdrh/pdrhparser.y
        OUTPUT  ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
        COMMENT "Generating ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c"
)

# setting propeties for the generated lexer and parser files
set_source_files_properties(${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c GENERATED PROPERTIES LANGUAGE CXX)
set_source_files_properties(${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c GENERATED PROPERTIES LANGUAGE CXX)
set_source_files_properties(${PROBREACH_BINARY_DIR}/git_sha1.cpp GENERATED PROPERTIES LANGUAGE CXX)


## create custom command for flex/lex (note the outputs)
#add_custom_command(
#        COMMAND ${FLEX_EXECUTABLE}
#        ARGS -o ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhlexer.c
#        ${PROBREACH_SOURCE_DIR}/pdrh2smt/parser/pdrhlexer.l
#        OUTPUT  ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhlexer.c
#        COMMENT "Generating ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhlexer.c"
#)
#
## create custom command for bison/yacc (note the DEPENDS)
#add_custom_command(
#        COMMAND ${BISON_EXECUTABLE}
#        ARGS -d -y ${PROBREACH_SOURCE_DIR}/pdrh2smt/parser/pdrhparser.y
#        -o ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhparser.c
#        DEPENDS ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhlexer.c
#        OUTPUT  ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhparser.c
#        COMMENT "Generating ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhparser.c"
#)
#
## setting propeties for the generated lexer and parser files
#set_source_files_properties(${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhparser.c GENERATED PROPERTIES LANGUAGE CXX)
#set_source_files_properties(${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhlexer.c GENERATED PROPERTIES LANGUAGE CXX)

MAKE_DIRECTORY(${PROBREACH_BINARY_DIR}/pdrh2smt/parser)

BISON_TARGET(pdrh_parser ${PROBREACH_SOURCE_DIR}/pdrh2smt/parser/pdrhparser.y ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhparser.cpp)
FLEX_TARGET(pdrh_scanner ${PROBREACH_SOURCE_DIR}/pdrh2smt/parser/pdrhlexer.l  ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhlexer.cpp)
ADD_FLEX_BISON_DEPENDENCY(pdrh_scanner pdrh_parser)


# header files
include_directories("${DREAL_INCLUDE_DIR}")
include_directories("${DREAL_INCLUDE_DIR}/ibex")
include_directories("${PROBREACH_SOURCE_DIR}/pdrh2smt")
include_directories("${PROBREACH_BINARY_DIR}/pdrh2smt/parser")
include_directories("${PROBREACH_SOURCE_DIR}")
include_directories("${PROBREACH_SOURCE_DIR}/util")
include_directories("${PROBREACH_SOURCE_DIR}/solver")
include_directories("${PROBREACH_SOURCE_DIR}/parser/csv")
include_directories("${PROBREACH_SOURCE_DIR}/parser/output")
include_directories("${PROBREACH_SOURCE_DIR}/parser/pdrh")
include_directories("${PROBREACH_SOURCE_DIR}/logging")
include_directories("${PROBREACH_BINARY_DIR}/parser/pdrh")

# Building ProbReach
# putting all source files together
file(GLOB PROBREACH_SRC   ${PROBREACH_SOURCE_DIR}/util/*.cpp
        ${PROBREACH_SOURCE_DIR}/parser/csv/*.cpp
        ${PROBREACH_SOURCE_DIR}/parser/output/*.cpp
        ${PROBREACH_SOURCE_DIR}/solver/*.cpp)

file(GLOB PROBREACH_INCLUDE   ${PROBREACH_SOURCE_DIR}/util/*.h
        ${PROBREACH_SOURCE_DIR}/parser/csv/*.h
        ${PROBREACH_SOURCE_DIR}/parser/output/*.h
        ${PROBREACH_SOURCE_DIR}/solver/*.h)

set(PROBREACH_INCLUDE ${PROBREACH_INCLUDE} ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.h)

set(PROBREACH_SRC ${PROBREACH_SRC}    ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
        ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
        ${PROBREACH_BINARY_DIR}/git_sha1.cpp)

# creating a library
add_library(probreach ${PROBREACH_SRC})
target_link_libraries(probreach ${DREAL_LIBRARIES} -lfl -lgsl -lgslcblas)

set(PDRH2SMT_SRC
        ${PROBREACH_SOURCE_DIR}/pdrh2smt/node.cpp
        ${PROBREACH_SOURCE_DIR}/pdrh2smt/model.cpp
        ${PROBREACH_SOURCE_DIR}/pdrh2smt/mode.cpp
        ${PROBREACH_SOURCE_DIR}/pdrh2smt/jump.cpp
        ${PROBREACH_SOURCE_DIR}/pdrh2smt/smt2_generator.cpp
        ${PROBREACH_SOURCE_DIR}/pdrh2smt/isat_generator.cpp
        ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhparser.cpp
        ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhlexer.cpp)

set(PDRH2SMT_INCLUDE
        ${PROBREACH_SOURCE_DIR}/pdrh2smt/node.h
        ${PROBREACH_SOURCE_DIR}/pdrh2smt/model.h
        ${PROBREACH_SOURCE_DIR}/pdrh2smt/mode.h
        ${PROBREACH_SOURCE_DIR}/pdrh2smt/jump.h
        ${PROBREACH_SOURCE_DIR}/pdrh2smt/smt2_generator.h
        ${PROBREACH_SOURCE_DIR}/pdrh2smt/isat_generator.h)

add_library(pdrh2smt ${PDRH2SMT_SRC})
target_link_libraries(pdrh2smt -lfl)
file(COPY ${PDRH2SMT_INCLUDE} DESTINATION ${PROBREACH_BINARY_DIR}/include/pdrh2smt)
make_directory(${PROBREACH_BINARY_DIR}/include/pdrh2smt/parser)
add_custom_command(TARGET pdrh2smt
        POST_BUILD
        COMMAND ${CMAKE_COMMAND} -E copy ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhparser.hpp ${PROBREACH_BINARY_DIR}/include/pdrh2smt/parser)
#install(FILES ${PDRH2SMT_INCLUDE} DESTINATION ${PROBREACH_BINARY_DIR}/include/pdrh2smt)

# adding executable
add_executable(ProbReach ${PROBREACH_SOURCE_DIR}/main.cpp)
target_compile_options(ProbReach PRIVATE -static)
target_link_libraries(ProbReach probreach)


install(FILES ${PROBREACH_INCLUDE} DESTINATION ${PROBREACH_BINARY_DIR}/include/probreach)
install(TARGETS ProbReach DESTINATION ${CMAKE_SOURCE_DIR}/bin)

# this is for CLion IDE
add_custom_target(install_probreach
        $(MAKE) install
        DEPENDS ProbReach
        COMMENT "Installing ProbReach")

if(GTEST_FOUND)
    # Building tests
    enable_testing()

    # setting the output directory for ProbReach
    set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${PROBREACH_BINARY_DIR}/test)

    # unit test for box.cpp
    add_executable(box_test ${PROBREACH_TEST_DIR}/util/box_test.cpp
            ${PROBREACH_TEST_DIR}/main_test.cpp
            ${PROBREACH_SOURCE_DIR}/util/box.cpp)
    target_link_libraries(box_test ${DREAL_LIBRARIES} -lgtest)
    add_test(box_test ${PROBREACH_BINARY_DIR}/test/box_test)

    # unit test for box_factory.cpp
    #add_executable(box_factory_test ${PROBREACH_TEST_DIR}/util/box_factory_test.cpp
    #        ${PROBREACH_TEST_DIR}/main_test.cpp
    #        ${PROBREACH_SOURCE_DIR}/util/box.cpp
    #        ${PROBREACH_SOURCE_DIR}/util/box_factory.cpp)
    #target_link_libraries(box_test ${DREAL_LIBRARIES} -lgtest)
    #add_test(box_factory_test ${PROBREACH_BINARY_DIR}/test/box_factory_test)

    # unit test for node.cpp
    add_executable(node_test ${PROBREACH_TEST_DIR}/pdrh2smt/node_test.cpp
            ${PROBREACH_TEST_DIR}/main_test.cpp
            ${PROBREACH_SOURCE_DIR}/pdrh2smt/node.cpp)
    target_link_libraries(node_test ${DREAL_LIBRARIES} -lgtest)
    add_test(node_test ${PROBREACH_BINARY_DIR}/test/node_test)

    # unit test for pdrhparser.cpp
    add_executable(pdrhparser_test ${PROBREACH_TEST_DIR}/pdrh2smt/parser/pdrhparser_test.cpp
            ${PROBREACH_TEST_DIR}/main_test.cpp
            ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhparser.cpp
            ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhlexer.cpp
            ${PROBREACH_SOURCE_DIR}/pdrh2smt/node.cpp
            ${PROBREACH_SOURCE_DIR}/pdrh2smt/mode.cpp
            ${PROBREACH_SOURCE_DIR}/pdrh2smt/jump.cpp
            ${PROBREACH_SOURCE_DIR}/pdrh2smt/model.cpp
            ${PROBREACH_SOURCE_DIR}/pdrh2smt/smt2_generator.cpp)
    target_link_libraries(pdrhparser_test ${DREAL_LIBRARIES} -lgtest -lfl)
    add_test(pdrhparser_test ${PROBREACH_BINARY_DIR}/test/pdrhparser_test)

    # unit test for isat_generator.cpp
    add_executable(isat_generator_test ${PROBREACH_TEST_DIR}/pdrh2smt/isat_generator_test.cpp
            ${PROBREACH_TEST_DIR}/main_test.cpp
            ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhparser.cpp
            ${PROBREACH_BINARY_DIR}/pdrh2smt/parser/pdrhlexer.cpp
            ${PROBREACH_SOURCE_DIR}/pdrh2smt/node.cpp
            ${PROBREACH_SOURCE_DIR}/pdrh2smt/mode.cpp
            ${PROBREACH_SOURCE_DIR}/pdrh2smt/jump.cpp
            ${PROBREACH_SOURCE_DIR}/pdrh2smt/model.cpp
            ${PROBREACH_SOURCE_DIR}/pdrh2smt/isat_generator.cpp)
    target_link_libraries(isat_generator_test ${DREAL_LIBRARIES} -lgtest -lfl)
    add_test(isat_generator_test ${PROBREACH_BINARY_DIR}/test/isat_generator_test)

endif(GTEST_FOUND)
