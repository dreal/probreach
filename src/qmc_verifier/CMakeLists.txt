file(GLOB PROBREACH_QMC_SRC
        ${PROBREACH_SOURCE_DIR}/util/qmc.cpp
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
        ${PROBREACH_SOURCE_DIR}/util/generators/smt2_generator.cpp)

set(PROBREACH_QMC_SRC ${PROBREACH_QMC_SRC}
        ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
        ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
        ${PROBREACH_BINARY_DIR}/git_sha1.cpp)

add_library(probreach_qmc ${PROBREACH_QMC_SRC})
if(APPLE)
    target_link_libraries(probreach_qmc -ll)
else(APPLE)
    target_link_libraries(probreach_qmc -lfl)
endif(APPLE)
target_link_libraries(probreach_qmc ${GSL_LIBRARIES} ${CAPD_LIBRARIES})

add_executable(qmc_verifier ${PROBREACH_SOURCE_DIR}/qmc_verifier/main.cpp)
target_link_libraries(qmc_verifier probreach_qmc)
