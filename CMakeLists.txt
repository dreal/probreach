cmake_minimum_required (VERSION 2.6)
# project name
project (ProbReach)
# setting some variables
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3 -Wall -Wno-sign-compare --std=c++11 -fopenmp -frounding-math")
set(CMAKE_EXE_LINKER_FLAGS "-static-libgcc -static-libstdc++")
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${PROJECT_SOURCE_DIR}/build/release/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${PROJECT_SOURCE_DIR}/build/release/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${PROJECT_SOURCE_DIR}/build/release)
set(DREAL_DIR "/home/fedor/dreal3")
set(DREAL_REL_DIR "/home/fedor/dreal3/build/release")
set(GSL_INCLUDE_DIRS "/usr/include")
set(GSL_LIBRARIES "/usr/lib/libgsl.a" "/usr/lib/libgslcblas.a")
# setting ProbReach version
set (PROBREACH_VERSION_MAJOR 1)
set (PROBREACH_VERSION_MINOR 2)
set (PROBREACH_VERSION_PATCH 2)
set (PROBREACH_VERSION ${PROBREACH_VERSION_MAJOR}.${PROBREACH_VERSION_MINOR}.${PROBREACH_VERSION_PATCH})
configure_file (
  "${PROJECT_SOURCE_DIR}/src/version.h.in"
  "${PROJECT_SOURCE_DIR}/src/version.h"
  )
# BISON
find_package(BISON REQUIRED)
if(BISON_FOUND)
    BISON_TARGET(pdrh_parser ${PROJECT_SOURCE_DIR}/src/parser/pdrh/pdrhparser.y ${PROJECT_SOURCE_DIR}/build/release/pdrhparser.c)
endif(BISON_FOUND)
# FLEX
find_package(FLEX REQUIRED)
if(FLEX_FOUND)
    FLEX_TARGET(pdrh_lexer ${PROJECT_SOURCE_DIR}/src/parser/pdrh/pdrhlexer.l  ${PROJECT_SOURCE_DIR}/build/release/pdrhlexer.c)
    ADD_FLEX_BISON_DEPENDENCY(pdrh_lexer pdrh_parser)
endif(FLEX_FOUND)
# setting propeties for the generated lexer and parser files
set_source_files_properties(${PROJECT_SOURCE_DIR}/build/release/pdrhparser.c GENERATED PROPERTIES LANGUAGE CXX)
set_source_files_properties(${PROJECT_SOURCE_DIR}/build/release/pdrhlexer.c GENERATED PROPERTIES LANGUAGE CXX)
# header files
include_directories("${DREAL_REL_DIR}/include/ibex")
include_directories("${DREAL_REL_DIR}/include")
include_directories("${PROJECT_SOURCE_DIR}/src")
include_directories("${PROJECT_SOURCE_DIR}/src/logging")
include_directories("${PROJECT_SOURCE_DIR}/src/solver")
include_directories("${PROJECT_SOURCE_DIR}/src/parser/csv")
include_directories("${PROJECT_SOURCE_DIR}/src/xml")
include_directories("${PROJECT_SOURCE_DIR}/build/release")
include_directories("${GSL_INCLUDE_DIRS}")
# putting all source files together
file(GLOB SOURCES   ${PROJECT_SOURCE_DIR}/src/*.cpp
                    ${PROJECT_SOURCE_DIR}/src/xml/*.cpp
                    ${PROJECT_SOURCE_DIR}/src/parser/csv/*.cpp
                    ${PROJECT_SOURCE_DIR}/src/solver/*.cpp
                    ${PROJECT_SOURCE_DIR}/build/release/*.c)
# setting executable
add_executable(ProbReach ${SOURCES})
# linking libraries
target_link_libraries(ProbReach ${DREAL_REL_DIR}/lib/libcapd.a)
target_link_libraries(ProbReach ${DREAL_REL_DIR}/lib/libibex.a)
target_link_libraries(ProbReach ${DREAL_REL_DIR}/lib/libprim.a)
target_link_libraries(ProbReach ${GSL_LIBRARIES})
# flag for FLEX
target_link_libraries(ProbReach -lfl)
