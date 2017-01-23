cmake_minimum_required(VERSION 2.6)
# project name
project(ProbReach)

# checking for packages
find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

# setting compiler flags
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3 -Wall -Wno-sign-compare -Wno-unused-variable -Wno-return-type -Wno-unused-function --std=c++11 -fopenmp -frounding-math")
set(CMAKE_EXE_LINKER_FLAGS "-static-libgcc -static-libstdc++")

# setting some environment variables
set(PROBREACH_SOURCE_DIR ${PROJECT_SOURCE_DIR}/src)
set(PROBREACH_BINARY_DIR ${PROJECT_SOURCE_DIR}/build/release)
set(PROBREACH_TEST_DIR ${PROJECT_SOURCE_DIR}/test)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${PROJECT_SOURCE_DIR}/build/release)

# checking if dReal binary is set
if(NOT DEFINED DREAL_DIR)
    message(WARNING "The variable DREAL_DIR is not defined. The default value \"$ENV{HOME}/dreal\" will be set")
    set(DREAL_DIR $ENV{HOME}/dreal)
endif(NOT DEFINED DREAL_DIR)

if(NOT DEFINED DREAL_REL_DIR)
    if(EXISTS ${DREAL_DIR}/build/release)
        set(DREAL_REL_DIR ${DREAL_DIR}/build/release)
    elseif(EXISTS ${DREAL_DIR}/build/minsizerel)
        set(DREAL_REL_DIR ${DREAL_DIR}/build/minsizerel)
    else(EXISTS ${DREAL_DIR}/build/release)
        message(FATAL_ERROR "dReal build not was not found at ${DREAL_DIR}/build/release or ${DREAL_DIR}/build/minsizerel. Please set the variable DREAL_REL_DIR with the full path to dReal build")
    endif(EXISTS ${DREAL_DIR}/build/release)
endif(NOT DEFINED DREAL_REL_DIR)

# getting git commit as a string
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${PROJECT_SOURCE_DIR}/cmake/Modules/")
include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)
configure_file(
        "${PROBREACH_SOURCE_DIR}/util/git_sha1.cpp.in"
        "${PROBREACH_BINARY_DIR}/git_sha1.cpp" @ONLY)

# setting ProbReach version
set(PROBREACH_VERSION_MAJOR 1)
set(PROBREACH_VERSION_MINOR 4)

set(PROBREACH_VERSION ${PROBREACH_VERSION_MAJOR}.${PROBREACH_VERSION_MINOR})
configure_file(
        "${PROBREACH_SOURCE_DIR}/version.h.in"
        "${PROBREACH_SOURCE_DIR}/version.h"
)

# setting solver binary
set(DREAL_BIN ${DREAL_DIR}/bin/dReal)
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

# header files
include_directories("${DREAL_REL_DIR}/include/ibex")
include_directories("${DREAL_REL_DIR}/include")
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

set(PROBREACH_SRC ${PROBREACH_SRC}    ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
        ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
        ${PROBREACH_BINARY_DIR}/git_sha1.cpp)

# adding executable
add_executable(ProbReach ${PROBREACH_SRC} ${PROBREACH_SOURCE_DIR}/main.cpp)

# creating a bin folder and copying ProbReach binary there
add_custom_command(TARGET ProbReach POST_BUILD
        COMMAND ${CMAKE_COMMAND} -E make_directory ${PROBREACH_SOURCE_DIR}/../bin
        COMMAND ${CMAKE_COMMAND} -E copy ${PROBREACH_BINARY_DIR}/ProbReach ${PROBREACH_SOURCE_DIR}/../bin
        COMMENT "Copying ${PROBREACH_BINARY_DIR}/ProbReach to ${PROBREACH_SOURCE_DIR}/../bin")

# linking libraries
target_link_libraries(ProbReach ${DREAL_REL_DIR}/lib/libcapd.a)
target_link_libraries(ProbReach ${DREAL_REL_DIR}/lib/libibex.a)
target_link_libraries(ProbReach ${DREAL_REL_DIR}/lib/libprim.a)
# flag for FLEX and GSL
target_link_libraries(ProbReach -lfl -lgsl -lgslcblas)
#adding static flag for ProbReach
set_target_properties(ProbReach PROPERTIES COMPILE_FLAGS "-static" )


# Building ProbReachTest
# putting all test files together
file(GLOB PROBREACH_TEST ${PROBREACH_TEST_DIR}/main_test.cpp
        ${PROBREACH_TEST_DIR}/util/*.cpp)

add_executable(ProbReachTest ${PROBREACH_TEST} ${PROBREACH_SRC})
target_link_libraries(ProbReachTest ${DREAL_REL_DIR}/lib/libcapd.a)
target_link_libraries(ProbReachTest ${DREAL_REL_DIR}/lib/libibex.a)
target_link_libraries(ProbReachTest ${DREAL_REL_DIR}/lib/libprim.a)
# flag for FLEX and GSL
target_link_libraries(ProbReachTest -lfl -lgsl -lgslcblas -lgtest)