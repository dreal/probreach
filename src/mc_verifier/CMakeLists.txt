file(GLOB PROBREACH_MC_SRC
        ${PROBREACH_SOURCE_DIR}/util/mc.cpp
        ${PROBREACH_SOURCE_DIR}/util/rnd.cpp
        ${PROBREACH_SOURCE_DIR}/util/ap.cpp
        ${PROBREACH_SOURCE_DIR}/util/model.cpp
        ${PROBREACH_SOURCE_DIR}/util/pdrh2box.cpp
        ${PROBREACH_SOURCE_DIR}/util/box.cpp
        ${PROBREACH_SOURCE_DIR}/util/pdrh_config.cpp
        ${PROBREACH_SOURCE_DIR}/util/box_factory.cpp
        ${PROBREACH_SOURCE_DIR}/util/measure.cpp
        ${PROBREACH_SOURCE_DIR}/util/node.cpp
        ${PROBREACH_SOURCE_DIR}/util/decision_procedure.cpp
        ${PROBREACH_SOURCE_DIR}/solver/dreal_wrapper.cpp
        ${PROBREACH_SOURCE_DIR}/util/generators/smt2_generator.cpp
        ${PROBREACH_SOURCE_DIR}/stability/stability.cpp)

set(PROBREACH_MC_SRC ${PROBREACH_MC_SRC}
        ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
        ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
        ${PROBREACH_BINARY_DIR}/git_sha1.cpp)

add_library(probreach_mc ${PROBREACH_MC_SRC})
if(APPLE)
    target_link_libraries(probreach_mc -ll)
else(APPLE)
    target_link_libraries(probreach_mc -lfl)
endif(APPLE)
target_link_libraries(probreach_mc ${GSL_LIBRARIES} ${CAPD_LIBRARIES} ${MATLAB_LIBRARIES})

add_executable(mc_verifier ${PROBREACH_SOURCE_DIR}/mc_verifier/main.cpp)
target_link_libraries(mc_verifier probreach_mc)
