file(GLOB PROBREACH_FORMAL_SRC
        ${PROBREACH_SOURCE_DIR}/util/formal.cpp
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

set(PROBREACH_FORMAL_SRC ${PROBREACH_FORMAL_SRC}
        ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
        ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
        ${PROBREACH_BINARY_DIR}/git_sha1.cpp)

add_library(probreach_formal ${PROBREACH_FORMAL_SRC})
add_dependencies(probreach_formal capd)

if(APPLE)
    target_link_libraries(probreach_formal -ll)
else(APPLE)
    target_link_libraries(probreach_formal -lfl)
endif(APPLE)

target_link_libraries(probreach_formal ${CAPD_LIBRARIES})

add_executable(formal_verifier ${PROBREACH_SOURCE_DIR}/formal_verifier/main.cpp)
target_link_libraries(formal_verifier probreach_formal)
