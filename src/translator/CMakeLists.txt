# adding executable
# If Matlab is installed on the target machine, link its libraries
IF(MATLAB_FOUND)
    message(STATUS "MATLAB Found, MATLAB MEX will be additionally compiled to enable Simulink Translator.")

    INCLUDE_DIRECTORIES(${MATLAB_INCLUDE_DIR})

    message(STATUS "MATLAB root dir: $ENV{MATLAB_ROOT}")
    message(STATUS "OUTPUT DIR: ${PROBREACH_BINARY_DIR}")
    message(STATUS "MATLAB include dir: ${MATLAB_INCLUDE_DIR}")
    message(STATUS "MATLAB libraries included: ${MATLAB_LIBRARIES}")

    file(GLOB PDRH2SIMULINK_SRC
            ${PROBREACH_SOURCE_DIR}/util/pdrh.cpp
            ${PROBREACH_SOURCE_DIR}/util/pdrh_config.cpp
            ${PROBREACH_SOURCE_DIR}/translator/*.cpp)

    file(GLOB PDRH2SIMULINK_INCLUDE
            ${PROBREACH_SOURCE_DIR}/util/pdrh.h
            ${PROBREACH_SOURCE_DIR}/util/pdrh_config.cpp
            ${PROBREACH_SOURCE_DIR}/translator/*.h)

    set(PDRH2SIMULINK_INCLUDE ${PDRH2SIMULINK_INCLUDE} ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.h)

    set(PDRH2SIMULINK_SRC ${PDRH2SIMULINK_SRC}    ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
            ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
            ${PROBREACH_BINARY_DIR}/git_sha1.cpp)

    add_library(pdrh2simulink_lib ${PDRH2SIMULINK_SRC})
    target_link_libraries(pdrh2simulink_lib -lfl)

    add_executable(pdrh2simulink ${PROBREACH_SOURCE_DIR}/translator/translator_main.cpp)
    target_compile_options(pdrh2simulink PRIVATE)
    target_link_libraries(pdrh2simulink pdrh2simulink_lib ${MATLAB_LIBRARIES})
ELSE(MATLAB_FOUND)
    MESSAGE("MATLAB not found, translator functionality won't be available.")
ENDIF(MATLAB_FOUND)
