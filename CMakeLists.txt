cmake_minimum_required (VERSION 2.6)
# BISON
#add_custom_command(
#   SOURCE ${PROJECT_SOURCE_DIR}/src/parser/pdrh/pdrhparser.y
#   COMMAND ${BISON_EXECUTABLE}
#   ARGS -d ${PROJECT_SOURCE_DIR}/src/parser/pdrh/pdrhparser.y
#        -o ${PROJECT_SOURCE_DIR}/src/parser/pdrh/pdrhparser.c
#   TARGET ProbReach
#   DEPENDS ${PROJECT_SOURCE_DIR}/src/parser/pdrh/pdrhlexer.c
#   OUTPUTS ${PROJECT_SOURCE_DIR}/src/parser/pdrh/pdrhparser.c)

# FLEX
#add_custom_command(
#   SOURCE ${PROJECT_SOURCE_DIR}/src/parser/pdrh/pdrhlexer.l
#   COMMAND ${FLEX_EXECUTABLE}
#   ARGS -o ${PROJECT_SOURCE_DIR}/src/parser/pdrh/pdrhlexer.c
#        ${PROJECT_SOURCE_DIR}/src/parser/pdrh/pdrhlexer.l
#   TARGET ProbReach
#   OUTPUTS ${PROJECT_SOURCE_DIR}/src/parser/pdrh/pdrhlexer.c)
project (ProbReach)
# setting some variables
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3 -Wall -Wno-sign-compare --std=c++11 -fopenmp -frounding-math")
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${PROJECT_SOURCE_DIR}/build/release/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${PROJECT_SOURCE_DIR}/build/release/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${PROJECT_SOURCE_DIR}/build/release)
set(DREAL_DIR "/home/fedor/dreal3")
# header files
include_directories("${DREAL_DIR}/build/release/include/ibex")
include_directories("${DREAL_DIR}/build/release/include")
include_directories("${PROJECT_SOURCE_DIR}/src")
include_directories("${PROJECT_SOURCE_DIR}/src/logging")
include_directories("${PROJECT_SOURCE_DIR}/src/solver")
include_directories("${PROJECT_SOURCE_DIR}/src/parser/csv")
include_directories("${PROJECT_SOURCE_DIR}/src/xml")
include_directories("${PROJECT_SOURCE_DIR}/build/release/")
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
# Boost
#find_package(Boost)
#if(Boost_FOUND)
#    include_directories(${Boost_INCLUDE_DIRS})
#    message(WARNING ${Boost_INCLUDE_DIRS})
#    target_link_libraries(ProbReach ${Boost_LIBRARIES})
#endif(Boost_FOUND)
# setting propeties for the fgenerated lexer and parser files
set_source_files_properties(${PROJECT_SOURCE_DIR}/build/release/pdrhparser.c GENERATED PROPERTIES LANGUAGE CXX)
set_source_files_properties(${PROJECT_SOURCE_DIR}/build/release/pdrhlexer.c GENERATED PROPERTIES LANGUAGE CXX)
# setting ProbReach version
set (PROBREACH_VERSION_MAJOR 1)
set (PROBREACH_VERSION_MINOR 2)
set (PROBREACH_VERSION_PATCH 2)
set (PROBREACH_VERSION ${PROBREACH_VERSION_MAJOR}.${PROBREACH_VERSION_MINOR}.${PROBREACH_VERSION_PATCH})
configure_file (
  "${PROJECT_SOURCE_DIR}/src/version.h.in"
  "${PROJECT_SOURCE_DIR}/src/version.h"
  )
# putting all source files together
file(GLOB SOURCES   ${PROJECT_SOURCE_DIR}/src/*.cpp
                    ${PROJECT_SOURCE_DIR}/src/xml/*.cpp
                    ${PROJECT_SOURCE_DIR}/src/parser/csv/*.cpp
                    ${PROJECT_SOURCE_DIR}/src/solver/*.cpp
                    ${PROJECT_SOURCE_DIR}/build/release/*.c)
# setting executable
add_executable(ProbReach ${SOURCES} src/parser/csv/csvparser.h src/parser/csv/csvparser.cpp)
# linking libraries
target_link_libraries(ProbReach /home/fedor/dreal3/build/release/lib/libcapd.a)
target_link_libraries(ProbReach /home/fedor/dreal3/build/release/lib/libibex.a)
target_link_libraries(ProbReach /home/fedor/dreal3/build/release/lib/libprim.a)
target_link_libraries(ProbReach /home/fedor/dreal3/build/release/lib/libdreal.a)
# flag for FLEX
target_link_libraries(ProbReach -lfl)
