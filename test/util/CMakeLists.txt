enable_testing()

include_directories("${PROBREACH_SOURCE_DIR}/util")

# setting the output directory for ProbReach
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${PROBREACH_BINARY_DIR}/test/util")

# unit test for box.cpp
add_executable(box_test ${PROBREACH_TEST_DIR}/util/box_test.cpp
        ${PROBREACH_TEST_DIR}/main_test.cpp
        ${PROBREACH_SOURCE_DIR}/util/box.cpp)
target_link_libraries(box_test ${CAPD_LIBRARIES} -lgtest)
add_test(box_test "${PROBREACH_BINARY_DIR}/test/util/box_test")

# unit test for the methods in node.cpp
add_executable(node_test ${PROBREACH_TEST_DIR}/util/node_test.cpp
        ${PROBREACH_TEST_DIR}/main_test.cpp
        ${PROBREACH_SOURCE_DIR}/util/node.cpp)
target_link_libraries(node_test -lgtest)
add_test(node_test "${PROBREACH_BINARY_DIR}/test/util/node_test")
