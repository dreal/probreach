#file(GLOB GP_SRC
#        ${PROBREACH_SOURCE_DIR}/util/decision_procedure.cpp
#        ${PROBREACH_SOURCE_DIR}/util/model.cpp
#        ${PROBREACH_SOURCE_DIR}/util/naive.cpp)

#file(GLOB SIMULATOR_INCLUDE
#        ${PROBREACH_SOURCE_DIR}/util/decision_procedure.h
#        ${PROBREACH_SOURCE_DIR}/util/model.cpp
#        ${PROBREACH_SOURCE_DIR}/util/naive.h)

include(${CMAKE_CURRENT_SOURCE_DIR}/src/eppr/CMakeLists.txt)

include_directories("${PROBREACH_SOURCE_DIR}/eppr")

#set(SIMULATOR_INCLUDE ${SIMULATOR_INCLUDE} ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.h)

#set(SIMULATOR_SRC ${SIMULATOR_SRC} ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
#        ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
#        ${PROBREACH_BINARY_DIR}/git_sha1.cpp)

#add_library(simulator_lib ${SIMULATOR_SRC})
#target_link_libraries(simulator_lib -lfl)

add_executable(gp ${PROBREACH_SOURCE_DIR}/gp/main.cpp)
#target_compile_options(gp PRIVATE)
target_link_libraries(gp eppr_lib)
