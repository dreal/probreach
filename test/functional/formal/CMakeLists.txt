enable_testing()

include_directories("${PROBREACH_SOURCE_DIR}/")
include_directories("${PROBREACH_SOURCE_DIR}/util")
include_directories("${PROBREACH_SOURCE_DIR}/parser/pdrh")

# setting the output directory for ProbReach
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${PROBREACH_BINARY_DIR}/test/functional/formal")

# functional test for formal verifier on different variants of good.pdrh
add_executable(formal_good_test ${PROBREACH_TEST_DIR}/functional/formal/good_test.cpp
        ${PROBREACH_TEST_DIR}/main_test.cpp)
target_link_libraries(formal_good_test probreach_formal -lgtest)
add_test(formal_good_test "${PROBREACH_BINARY_DIR}/test/functional/formal/formal_good_test")

