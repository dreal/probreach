cmake_minimum_required(VERSION 2.6)
# project name
project(ProbReach)

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${PROJECT_SOURCE_DIR}/cmake/Modules/")

# checking for packages
find_package(CAPD)
find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)
find_package(GSL)
find_package(GTest)
# Needed for using the translator tool
find_package(Matlab)

# setting compiler flags
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3 -std=c++11 -fopenmp -frounding-math -fPIC")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wno-sign-compare -Wno-unused-variable -Wno-return-type -Wno-unused-function")
#set(CMAKE_EXE_LINKER_FLAGS "-static-libgcc -static-libstdc++")

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
        COMMENT "Generating ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c")

# create custom command for bison/yacc (note the DEPENDS)
add_custom_command(
        COMMAND ${BISON_EXECUTABLE}
        ARGS -d -y ${PROBREACH_SOURCE_DIR}/parser/pdrh/pdrhparser.y
        -o ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
        DEPENDS ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
        DEPENDS ${PROBREACH_SOURCE_DIR}/parser/pdrh/pdrhparser.y
        OUTPUT  ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
        COMMENT "Generating ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c")

# setting propeties for the generated lexer and parser files
set_source_files_properties(${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c GENERATED PROPERTIES LANGUAGE CXX)
set_source_files_properties(${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c GENERATED PROPERTIES LANGUAGE CXX)
set_source_files_properties(${PROBREACH_BINARY_DIR}/git_sha1.cpp GENERATED PROPERTIES LANGUAGE CXX)

set(PROBREACH_VERSION ${PROBREACH_VERSION_MAJOR}.${PROBREACH_VERSION_MINOR})
configure_file(
        "${PROBREACH_SOURCE_DIR}/version.h.in"
        "${PROBREACH_SOURCE_DIR}/version.h")

IF(CAPD_FOUND)
    include_directories("${CAPD_INCLUDE_DIR}")
ELSE(CAPD_FOUND)
    message(STATUS "CAPD libraries not found, option to build ProbReach won't be available. Refer to installation guide available on Github or ./doc/build")
ENDIF(CAPD_FOUND)

include_directories("${PROBREACH_SOURCE_DIR}")
include_directories("${PROBREACH_SOURCE_DIR}/util")
include_directories("${PROBREACH_SOURCE_DIR}/util/generators")
include_directories("${PROBREACH_SOURCE_DIR}/stability")
include_directories("${PROBREACH_SOURCE_DIR}/parser/csv")
include_directories("${PROBREACH_SOURCE_DIR}/parser/output")
include_directories("${PROBREACH_SOURCE_DIR}/parser/pdrh")
include_directories("${PROBREACH_SOURCE_DIR}/solver")
include_directories("${PROBREACH_SOURCE_DIR}/logging")
include_directories("${PROBREACH_BINARY_DIR}/parser/pdrh")


# Adds the option to build the translator if MATLAB is located
include(${CMAKE_CURRENT_SOURCE_DIR}/src/translator/CMakeLists.txt)
include(${CMAKE_CURRENT_SOURCE_DIR}/src/simulator/CMakeLists.txt)
include(${CMAKE_CURRENT_SOURCE_DIR}/src/pid_optimiser/CMakeLists.txt)
include(${CMAKE_CURRENT_SOURCE_DIR}/src/formal_verifier/CMakeLists.txt)
include(${CMAKE_CURRENT_SOURCE_DIR}/src/mc_verifier/CMakeLists.txt)
include(${CMAKE_CURRENT_SOURCE_DIR}/src/gp/CMakeLists.txt)
include(${CMAKE_CURRENT_SOURCE_DIR}/test/util/CMakeLists.txt)
