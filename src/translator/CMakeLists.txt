# adding executable
# If Matlab is installed on the target machine, link its libraries
IF(MATLAB_FOUND)
    message(STATUS "MATLAB found, compilation of pdrh2Simulink translator is enabled.")

    INCLUDE_DIRECTORIES(${MATLAB_INCLUDE_DIR})

    message(STATUS "MATLAB root dir: $ENV{MATLAB_ROOT}")
    message(STATUS "Output dir: ${PROBREACH_BINARY_DIR}")
    message(STATUS "MATLAB include dir: ${MATLAB_INCLUDE_DIR}")
    message(STATUS "MATLAB libraries included: ${MATLAB_LIBRARIES}")

    file(GLOB PDRH2SIMULINK_SRC
            ${PROBREACH_SOURCE_DIR}/util/node.cpp
            ${PROBREACH_SOURCE_DIR}/util/model.cpp
            ${PROBREACH_SOURCE_DIR}/util/pdrh_config.cpp
            ${PROBREACH_SOURCE_DIR}/translator/*.cpp)

    file(GLOB PDRH2SIMULINK_INCLUDE
            ${PROBREACH_SOURCE_DIR}/util/node.h
            ${PROBREACH_SOURCE_DIR}/util/model.h
            ${PROBREACH_SOURCE_DIR}/util/pdrh_config.cpp
            ${PROBREACH_SOURCE_DIR}/translator/*.h)

    set(PDRH2SIMULINK_INCLUDE ${PDRH2SIMULINK_INCLUDE} ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.h)

    set(PDRH2SIMULINK_SRC ${PDRH2SIMULINK_SRC}    ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
            ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
            ${PROBREACH_BINARY_DIR}/git_sha1.cpp)

    add_library(pdrh2simulink_lib ${PDRH2SIMULINK_SRC})
    if(APPLE)
        target_link_libraries(pdrh2simulink_lib -ll)
    else(APPLE)
        target_link_libraries(pdrh2simulink_lib -lfl)
    endif(APPLE)

    add_executable(pdrh2simulink ${PROBREACH_SOURCE_DIR}/translator/translator_main.cpp)
    target_compile_options(pdrh2simulink PRIVATE)
    target_link_libraries(pdrh2simulink pdrh2simulink_lib ${MATLAB_LIBRARIES})
ELSE(MATLAB_FOUND)
    MESSAGE(WARNING "MATLAB not found, translator functionality won't be available.")
ENDIF(MATLAB_FOUND)
