cmake_minimum_required(VERSION 2.6)

find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

include_directories(".")

set(PDRH2SMT_SRC node.cpp model.cpp mode.cpp jump.cpp smt2_generator.cpp isat_generator.cpp
        ${CMAKE_BINARY_DIR}/parser/pdrhparser.cpp ${CMAKE_BINARY_DIR}/parser/pdrhlexer.cpp)

set(PDRH2SMT_INCLUDE node.h model.h mode.h jump.h smt2_generator.h isat_generator.h
        ${CMAKE_BINARY_DIR}/parser/pdrhparser.hpp ${CMAKE_BINARY_DIR}/parser/pdrhlexer.hpp)

make_directory(${CMAKE_BINARY_DIR}/parser)
bison_target(pdrh_parser parser/pdrhparser.y ${CMAKE_BINARY_DIR}/parser/pdrhparser.cpp)
flex_target(pdrh_scanner parser/pdrhlexer.l  ${CMAKE_BINARY_DIR}/parser/pdrhlexer.cpp)
add_flex_bison_dependency(pdrh_scanner pdrh_parser)

add_library(pdrh2smt ${PDRH2SMT_SRC})
target_link_libraries(pdrh2smt -lfl)

#file(COPY ${PDRH2SMT_INCLUDE} DESTINATION include)
#make_directory(include/parser)
#add_custom_command(TARGET pdrh2smt
#        POST_BUILD
#        COMMAND ${CMAKE_COMMAND} -E copy parser/pdrhparser.hpp include/parser)
#install(FILES ${PDRH2SMT_INCLUDE} DESTINATION include/)