file(GLOB SIMULATOR_SRC
        ${PROBREACH_SOURCE_DIR}/util/node.cpp
        ${PROBREACH_SOURCE_DIR}/util/model.cpp
        ${PROBREACH_SOURCE_DIR}/util/naive.cpp)

set(SIMULATOR_INCLUDE ${SIMULATOR_INCLUDE} ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.h)

set(SIMULATOR_SRC ${SIMULATOR_SRC} ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
        ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
        ${PROBREACH_BINARY_DIR}/git_sha1.cpp)

add_library(simulator_lib ${SIMULATOR_SRC})
target_link_libraries(simulator_lib -lfl)

add_executable(simulate ${PROBREACH_SOURCE_DIR}/simulator/main.cpp)
target_compile_options(simulate PRIVATE)
target_link_libraries(simulate simulator_lib)
