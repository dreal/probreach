file(GLOB EPPR_SRC
        ${PROBREACH_SOURCE_DIR}/eppr/*.cpp)

file(GLOB EPPR_INCLUDE
        ${PROBREACH_SOURCE_DIR}/eppr/*.h)

#set(EPPR_INCLUDE ${EPPR_INCLUDE} ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.h)

#set(EPPR_SRC ${EPPR_SRC} ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
#        ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
#        ${PROBREACH_BINARY_DIR}/git_sha1.cpp)

add_library(eppr_lib ${EPPR_SRC})
target_link_libraries(eppr_lib -lgsl -lgslcblas)

#add_executable(simulate ${PROBREACH_SOURCE_DIR}/simulator/main.cpp)
#target_compile_options(simulate PRIVATE)
#target_link_libraries(simulate simulator_lib)
