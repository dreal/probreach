cmake_minimum_required(VERSION 3.10)
# project name
project(ProbReach)

# setting path to additional cmake modules 
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${PROJECT_SOURCE_DIR}/cmake/Modules/")
include(${CMAKE_ROOT}/Modules/ExternalProject.cmake)

# setting install/build/test paths, etc.
set(PROBREACH_SOURCE_DIR ${CMAKE_SOURCE_DIR}/src)
set(PROBREACH_BINARY_DIR ${CMAKE_BINARY_DIR})
set(PROBREACH_TEST_DIR ${CMAKE_SOURCE_DIR}/test)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})

# setting version related variables (i.e., MAJOR, MINOR and GIT_SHA1)
set(PROBREACH_VERSION_MAJOR 1)
set(PROBREACH_VERSION_MINOR 4)
include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)
configure_file(
  "${PROBREACH_SOURCE_DIR}/util/git_sha1.cpp.in"
  "${PROBREACH_BINARY_DIR}/git_sha1.cpp" @ONLY)
set_source_files_properties(${PROBREACH_BINARY_DIR}/git_sha1.cpp GENERATED PROPERTIES LANGUAGE CXX)
set(PROBREACH_VERSION ${PROBREACH_VERSION_MAJOR}.${PROBREACH_VERSION_MINOR})
configure_file(
  "${PROBREACH_SOURCE_DIR}/version.h.in"
  "${PROBREACH_SOURCE_DIR}/version.h")

# setting compiler flags
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3 -std=c++14 -fopenmp -frounding-math -fPIC")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wno-sign-compare -Wno-unused-variable -Wno-return-type -Wno-unused-function")
#set(CMAKE_EXE_LINKER_FLAGS "-static-libgcc -static-libstdc++")


# building and installing PDRH lexer and parser
find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

# creating a directory for the lexer and parser files
add_custom_target(pdrhparser
  COMMAND ${CMAKE_COMMAND} -E make_directory ${PROBREACH_BINARY_DIR}/parser/pdrh
  COMMENT "Creating directory ${PROBREACH_BINARY_DIR}/parser/pdrh")
# create custom command for flex/lex (note the outputs)
add_custom_command(
  COMMAND ${FLEX_EXECUTABLE}
  ARGS -o ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
  ${PROBREACH_SOURCE_DIR}/parser/pdrh/pdrhlexer.l
  DEPENDS pdrhparser
  DEPENDS ${PROBREACH_SOURCE_DIR}/parser/pdrh/pdrhlexer.l
  OUTPUT  ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
  COMMENT "Generating ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c")

# create custom command for bison/yacc (note the DEPENDS)
add_custom_command(
  COMMAND ${BISON_EXECUTABLE}
  ARGS -d -y ${PROBREACH_SOURCE_DIR}/parser/pdrh/pdrhparser.y
  -o ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
  DEPENDS ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c
  DEPENDS ${PROBREACH_SOURCE_DIR}/parser/pdrh/pdrhparser.y
  OUTPUT  ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c
  COMMENT "Generating ${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c")

# setting propeties for the generated lexer and parser files
set_source_files_properties(${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhparser.c GENERATED PROPERTIES LANGUAGE CXX)
set_source_files_properties(${PROBREACH_BINARY_DIR}/parser/pdrh/pdrhlexer.c GENERATED PROPERTIES LANGUAGE CXX)
# including the parser directory
include_directories("${PROBREACH_BINARY_DIR}/parser/pdrh")

# building and installing CAPD
set(CAPD_BUILD_PATH ${PROBREACH_BINARY_DIR}/external CACHE INTERNAL "")
set(CAPD_INSTALL_PATH ${PROBREACH_BINARY_DIR} CACHE INTERNAL "")
find_package(CAPD)
IF(CAPD_FOUND)
  message(STATUS "Found CAPD (headers: ${CAPD_INCLUDE_DIR}; libs: ${CAPD_LIBRARIES})")
  add_custom_target(capd)
ELSE(CAPD_FOUND)
  set(CAPD_URL "https://sourceforge.net/projects/capd/files/5.1.2/src/capd-capdDynSys-5.1.2.tar.gz")
  message(STATUS "CAPD not found at ${CAPD_INSTALL_PATH}")
  message(STATUS ">>> CAPD version from ${CAPD_URL} will be automatically installed to ${CAPD_INSTALL_PATH}")
  message(STATUS ">>> If you want to specify a different location, please specify the following variables:")
  message(STATUS ">>>   CAPD_BUILD_PATH - path where CAPD will be built")
  message(STATUS ">>>   CAPD_INSTALL_PATH - path where CAPD headers and libraries will be installed")
  message(STATUS "")
  message(STATUS ">>> If you have a version of CAPD already installed on your system, please set the following variables:")
  message(STATUS ">>>   CAPD_INCLUDE_DIR - path to CAPD headers")
  message(STATUS ">>>   CAPD_LIBRARIES - path to \"libcapd.a\"")
  message(STATUS "")
  ExternalProject_Add(capd
    PREFIX ${CAPD_BUILD_PATH}
    URL ${CAPD_URL}
    UPDATE_COMMAND ""
    CONFIGURE_COMMAND ${CAPD_BUILD_PATH}/src/capd/configure
      C=${CMAKE_C_COMPILER}
      XX=${CMAKE_CXX_COMPILER}
      --prefix=${CAPD_INSTALL_PATH}
      --without-gui
	    --with-mpfr=no
      --with-filib=no
    BUILD_COMMAND make
    BUILD_IN_SOURCE 1
    LOG_DOWNLOAD 1
    LOG_UPDATE 1
    LOG_CONFIGURE 1
    LOG_BUILD 1
    LOG_TEST 1
    LOG_INSTALL 1
    INSTALL_COMMAND make install)
	
  set(CAPD_INCLUDE_DIR "${CAPD_INSTALL_PATH}/include")
  set(CAPD_LIBRARIES "${CAPD_INSTALL_PATH}/lib/libcapd.a")
	set(CAPD_FOUND ON)
ENDIF(CAPD_FOUND)
# including CAPD headers
include_directories("${CAPD_INCLUDE_DIR}")

# including all the ProbReach headers
include_directories("${PROBREACH_SOURCE_DIR}")
include_directories("${PROBREACH_SOURCE_DIR}/util")
include_directories("${PROBREACH_SOURCE_DIR}/util/generators")
include_directories("${PROBREACH_SOURCE_DIR}/stability")
include_directories("${PROBREACH_SOURCE_DIR}/parser/csv")
include_directories("${PROBREACH_SOURCE_DIR}/parser/output")
include_directories("${PROBREACH_SOURCE_DIR}/parser/pdrh")
include_directories("${PROBREACH_SOURCE_DIR}/solver")
include_directories("${PROBREACH_SOURCE_DIR}/logging")

# searching for GSL
find_package(GSL)
if(GSL_FOUND)
  include_directories("${GSL_INCLUDE_DIRS}")
endif(GSL_FOUND)

# adding CMakeLists.txt files that specify executables
include(${CMAKE_CURRENT_SOURCE_DIR}/src/simulator/CMakeLists.txt)
include(${CMAKE_CURRENT_SOURCE_DIR}/src/pid_optimiser/CMakeLists.txt)
include(${CMAKE_CURRENT_SOURCE_DIR}/src/formal_verifier/CMakeLists.txt)
include(${CMAKE_CURRENT_SOURCE_DIR}/src/mc_verifier/CMakeLists.txt)
include(${CMAKE_CURRENT_SOURCE_DIR}/src/qmc_verifier/CMakeLists.txt)
include(${CMAKE_CURRENT_SOURCE_DIR}/src/gp/CMakeLists.txt)
include(${CMAKE_CURRENT_SOURCE_DIR}/src/translator/CMakeLists.txt)

# enabling testing
find_package(GTest)
if(GTest_FOUND)
  include("${CMAKE_CURRENT_SOURCE_DIR}/test/CMakeLists.txt")
endif(GTest_FOUND)
