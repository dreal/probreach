cmake_minimum_required (VERSION 2.6)
project (ProbReach)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2 -Wall --std=c++11 -fopenmp -frounding-math")

include_directories("/home/fedor/dreal3/build/release/include/ibex")
include_directories("/home/fedor/dreal3/build/release/include")

file(GLOB SOURCES ${PROJECT_SOURCE_DIR}/src/*.cpp)

add_executable(ProbReach ${SOURCES} src/box_factory.cpp src/box_factory.cpp src/box_factory.h)
target_link_libraries(ProbReach /home/fedor/dreal3/build/release/lib/libcapd.a)
target_link_libraries(ProbReach /home/fedor/dreal3/build/release/lib/libibex.a)
target_link_libraries(ProbReach /home/fedor/dreal3/build/release/lib/libprim.a)
