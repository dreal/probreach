include(${CMAKE_CURRENT_SOURCE_DIR}/src/eppr/CMakeLists.txt)

include_directories("${PROBREACH_SOURCE_DIR}/eppr")

file(GLOB GP_SRC
        ${PROBREACH_SOURCE_DIR}/util/node.cpp
        ${PROBREACH_SOURCE_DIR}/util/model.cpp
        ${PROBREACH_SOURCE_DIR}/util/naive.cpp
        ${PROBREACH_SOURCE_DIR}/util/pdrh2box.cpp
        ${PROBREACH_SOURCE_DIR}/util/box.cpp
        ${PROBREACH_SOURCE_DIR}/util/mc.cpp
        ${PROBREACH_SOURCE_DIR}/util/pdrh_config.cpp
        ${PROBREACH_SOURCE_DIR}/util/box_factory.cpp
        ${PROBREACH_SOURCE_DIR}/util/measure.cpp
        ${PROBREACH_SOURCE_DIR}/util/rnd.cpp
        ${PROBREACH_SOURCE_DIR}/util/ap.cpp
        ${PROBREACH_SOURCE_DIR}/util/decision_procedure.cpp
        ${PROBREACH_SOURCE_DIR}/solver/dreal_wrapper.cpp
        ${PROBREACH_SOURCE_DIR}/util/generators/smt2_generator.cpp)

set(GP_INCLUDE ${GP_INCLUDE} ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.h)

set(GP_SRC ${GP_SRC} ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
        ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
        ${PROBREACH_BINARY_DIR}/git_sha1.cpp)

add_library(gp_lib ${GP_SRC})

if(APPLE)
    target_link_libraries(gp_lib -ll)
else(APPLE)
    target_link_libraries(gp_lib -lfl)
endif(APPLE)

target_link_libraries(gp_lib -lgsl -lgslcblas ${CAPD_LIBRARIES})

#add_library(simulator_lib ${SIMULATOR_SRC})
#target_link_libraries(simulator_lib -lfl)

add_executable(gp ${PROBREACH_SOURCE_DIR}/gp/main.cpp)
#target_compile_options(gp PRIVATE)
target_link_libraries(gp eppr_lib gp_lib)
