file(GLOB SIMULATOR_SRC
        ${PROBREACH_SOURCE_DIR}/util/node.cpp
        ${PROBREACH_SOURCE_DIR}/util/model.cpp
        ${PROBREACH_SOURCE_DIR}/util/naive.cpp)

set(SIMULATOR_INCLUDE ${SIMULATOR_INCLUDE} ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.h)

set(SIMULATOR_SRC ${SIMULATOR_SRC} ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
        ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
        ${PROBREACH_BINARY_DIR}/git_sha1.cpp)

add_library(probreach_naive ${SIMULATOR_SRC})
if(APPLE)
    target_link_libraries(probreach_naive -ll)
else(APPLE)
    target_link_libraries(probreach_naive -lfl)
endif(APPLE)

add_executable(simulator ${PROBREACH_SOURCE_DIR}/simulator/main.cpp)
target_link_libraries(simulator probreach_naive)
