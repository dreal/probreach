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
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3 -Wall -Wno-sign-compare -Wno-unused-variable -Wno-return-type -Wno-unused-function -static --std=c++11 -fopenmp -frounding-math")
set(CMAKE_EXE_LINKER_FLAGS "-static-libgcc -static-libstdc++")

# setting some environment variables
set(PROBREACH_SOURCE_DIR ${PROJECT_SOURCE_DIR}/src)
set(PROBREACH_BINARY_DIR ${PROJECT_SOURCE_DIR}/build/release)
set(PROBREACH_TEST_DIR ${PROJECT_SOURCE_DIR}/test)
#set(CMAKE_INSTALL_PREFIX ${PROJECT_SOURCE_DIR}/../bin)
#set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${PROJECT_SOURCE_DIR}/build/release)
#set(CMAKE_BUILD_FILES_DIRECTORY ${PROJECT_SOURCE_DIR}/build/release)
#set(CMAKE_BUILD_DIRECTORY ${PROJECT_SOURCE_DIR}/build/release)

# getting git commit as a string
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
include_directories("${DREAL_INCLUDE_DIR}")
include_directories("${DREAL_INCLUDE_DIR}/ibex")
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

# setting the output directory for ProbReach
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${PROBREACH_BINARY_DIR})

# creating a library
add_library(probreach ${PROBREACH_SRC})
target_link_libraries(probreach ${DREAL_LIBRARIES} -lfl -lgsl -lgslcblas)

# adding executable
add_executable(ProbReach ${PROBREACH_SOURCE_DIR}/main.cpp)
target_link_libraries(ProbReach probreach)

install(FILES ${PROBREACH_INCLUDE} DESTINATION ${PROBREACH_BINARY_DIR}/include)
install(TARGETS ProbReach DESTINATION ${PROBREACH_BINARY_DIR}/../../bin)
install(TARGETS probreach DESTINATION ${PROBREACH_BINARY_DIR}/lib)

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
#    add_executable(box_factory_test ${PROBREACH_TEST_DIR}/util/box_factory_test.cpp
#            ${PROBREACH_TEST_DIR}/main_test.cpp
#            ${PROBREACH_SOURCE_DIR}/util/box.cpp
#            ${PROBREACH_SOURCE_DIR}/util/box_factory.cpp)
#    target_link_libraries(box_test ${DREAL_LIBRARIES} -lgtest)
#    add_test(box_factory_test ${PROBREACH_BINARY_DIR}/test/box_factory_test)

    # unit test for box.cpp
    add_executable(node_test ${PROBREACH_TEST_DIR}/util/node_test.cpp
            ${PROBREACH_TEST_DIR}/main_test.cpp
            ${PROBREACH_SOURCE_DIR}/util/node.cpp)
    target_link_libraries(node_test ${DREAL_LIBRARIES} -lgtest)
    add_test(node_test ${PROBREACH_BINARY_DIR}/test/node_test)

endif(GTEST_FOUND)
