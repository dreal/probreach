cmake_minimum_required (VERSION 2.6)
project (ProbReach)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3 -Wall -Wno-sign-compare --std=c++11 -fopenmp -frounding-math")

include_directories("/home/fedor/dreal3/build/release/include/ibex")
include_directories("/home/fedor/dreal3/build/release/include")
include_directories("/home/fedor/dreal3/src/api")
include_directories("${PROJECT_SOURCE_DIR}/src")
include_directories("${PROJECT_SOURCE_DIR}/src/xml")

set (PROBREACH_VERSION_MAJOR 1)
set (PROBREACH_VERSION_MINOR 2)
set (PROBREACH_VERSION_PATCH 2)
set (PROBREACH_VERSION ${PROBREACH_VERSION_MAJOR}.${PROBREACH_VERSION_MINOR}.${PROBREACH_VERSION_PATCH})

# configure a header file to pass some of the CMake settings
# to the source code
configure_file (
  "${PROJECT_SOURCE_DIR}/src/version.h.in"
  "${PROJECT_SOURCE_DIR}/src/version.h"
  )

file(GLOB SOURCES ${PROJECT_SOURCE_DIR}/src/*.cpp ${PROJECT_SOURCE_DIR}/src/xml/*.cpp)

add_executable(ProbReach ${SOURCES} src/pdrh_config.cpp src/pdrh_config.h src/model.cpp src/model.h)
target_link_libraries(ProbReach /home/fedor/dreal3/build/release/lib/libcapd.a)
target_link_libraries(ProbReach /home/fedor/dreal3/build/release/lib/libibex.a)
target_link_libraries(ProbReach /home/fedor/dreal3/build/release/lib/libprim.a)
target_link_libraries(ProbReach /home/fedor/dreal3/build/release/lib/libdreal.a)
