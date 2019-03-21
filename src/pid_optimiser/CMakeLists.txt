#include_directories("${PROBREACH_SOURCE_DIR}/util")
#include_directories("${PROBREACH_SOURCE_DIR}/logging")
#
#
#file(GLOB PID_OPTIMISER_SRC
#        ${PROBREACH_SOURCE_DIR}/util/node.cpp
#        ${PROBREACH_SOURCE_DIR}/util/model.cpp
#        ${PROBREACH_SOURCE_DIR}/util/naive.cpp
#        ${PROBREACH_SOURCE_DIR}/util/pdrh2box.cpp
#        ${PROBREACH_SOURCE_DIR}/util/box.cpp
#        ${PROBREACH_SOURCE_DIR}/util/mc.cpp
#        ${PROBREACH_SOURCE_DIR}/util/pdrh_config.cpp
#        ${PROBREACH_SOURCE_DIR}/util/box_factory.cpp
#        ${PROBREACH_SOURCE_DIR}/util/measure.cpp
#        ${PROBREACH_SOURCE_DIR}/util/rnd.cpp
#        ${PROBREACH_SOURCE_DIR}/util/ap.cpp
#        ${PROBREACH_SOURCE_DIR}/util/decision_procedure.cpp
#        ${PROBREACH_SOURCE_DIR}/solver/dreal_wrapper.cpp
#        ${PROBREACH_SOURCE_DIR}/util/generators/smt2_generator.cpp)
#
#set(PID_OPTIMISER_INCLUDE ${PID_OPTIMISER_INCLUDE} ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.h)
#
#set(PID_OPTIMISER_SRC ${PID_OPTIMISER_SRC} ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
#        ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
#        ${PROBREACH_BINARY_DIR}/git_sha1.cpp)
#
#add_library(pid_optimiser_lib ${PID_OPTIMISER_SRC})
#target_link_libraries(pid_optimiser_lib -lfl -lgsl -lgslcblas ${CAPD_LIBRARIES})

add_executable(pid_optimiser ${PROBREACH_SOURCE_DIR}/pid_optimiser/main.cpp)
target_link_libraries(pid_optimiser probreach_mc)
