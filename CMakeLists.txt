cmake_minimum_required (VERSION 2.6)
project (ProbReach)

if(NOT DEFINED ${CAPD_CONFIG})
    set(CAPD_CONFIG /home/fedor/capd/capd/bin/capd-config)
endif(NOT DEFINED ${CAPD_CONFIG})

if(NOT DEFINED ${PKG_CONFIG})
    set(PKG_CONFIG /usr/bin/pkg-config)
endif(NOT DEFINED ${PKG_CONFIG})

execute_process(COMMAND ${CAPD_CONFIG} --cflags OUTPUT_VARIABLE CAPD_CXX_FLAGS OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND ${CAPD_CONFIG} --libs OUTPUT_VARIABLE CAPD_LIBS OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND ${PKG_CONFIG} --cflags ibex OUTPUT_VARIABLE IBEX_CXX_FLAGS OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND ${PKG_CONFIG} --libs ibex OUTPUT_VARIABLE IBEX_LIBS OUTPUT_STRIP_TRAILING_WHITESPACE)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2 -Wall --std=c++11 -fopenmp ${CAPD_CXX_FLAGS} ${IBEX_CXX_FLAGS}")

file(GLOB SOURCES ${PROJECT_SOURCE_DIR}/src/*.cpp)

add_executable(ProbReach ${SOURCES})
target_link_libraries(ProbReach "${IBEX_LIBS} ${CAPD_LIBS}")
