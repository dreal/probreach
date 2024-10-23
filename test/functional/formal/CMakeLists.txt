enable_testing()

include_directories("${PROBREACH_SOURCE_DIR}/")
include_directories("${PROBREACH_SOURCE_DIR}/util")
include_directories("${PROBREACH_SOURCE_DIR}/parser/pdrh")

# setting the output directory for ProbReach
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${PROBREACH_BINARY_DIR}/test/functional/formal")

add_executable(formal_good_test_1 
  ${PROBREACH_TEST_DIR}/functional/formal/good_test_1.cpp
  ${PROBREACH_TEST_DIR}/main_test.cpp)
target_link_libraries(formal_good_test_1 probreach_formal -lgtest)
add_test(formal_good_test_1 "${PROBREACH_BINARY_DIR}/test/functional/formal/formal_good_test_1")

add_executable(formal_good_test_2
  ${PROBREACH_TEST_DIR}/functional/formal/good_test_2.cpp
  ${PROBREACH_TEST_DIR}/main_test.cpp)
target_link_libraries(formal_good_test_2 probreach_formal -lgtest)
add_test(formal_good_test_2 "${PROBREACH_BINARY_DIR}/test/functional/formal/formal_good_test_2")

add_executable(formal_good_test_3 
  ${PROBREACH_TEST_DIR}/functional/formal/good_test_3.cpp
  ${PROBREACH_TEST_DIR}/main_test.cpp)
target_link_libraries(formal_good_test_3 probreach_formal -lgtest)
add_test(formal_good_test_3 "${PROBREACH_BINARY_DIR}/test/functional/formal/formal_good_test_3")

add_executable(formal_good_test_4 
  ${PROBREACH_TEST_DIR}/functional/formal/good_test_4.cpp
  ${PROBREACH_TEST_DIR}/main_test.cpp)
target_link_libraries(formal_good_test_4 probreach_formal -lgtest)
add_test(formal_good_test_4 "${PROBREACH_BINARY_DIR}/test/functional/formal/formal_good_test_4")

add_executable(formal_bad_test_1 
  ${PROBREACH_TEST_DIR}/functional/formal/bad_test_1.cpp
  ${PROBREACH_TEST_DIR}/main_test.cpp)
target_link_libraries(formal_bad_test_1 probreach_formal -lgtest)
add_test(formal_bad_test_1 "${PROBREACH_BINARY_DIR}/test/functional/formal/formal_bad_test_1")

add_executable(formal_bad_test_2 
  ${PROBREACH_TEST_DIR}/functional/formal/bad_test_2.cpp
  ${PROBREACH_TEST_DIR}/main_test.cpp)
target_link_libraries(formal_bad_test_2 probreach_formal -lgtest)
add_test(formal_bad_test_2 "${PROBREACH_BINARY_DIR}/test/functional/formal/formal_bad_test_2")

add_executable(formal_bad_test_3
  ${PROBREACH_TEST_DIR}/functional/formal/bad_test_3.cpp
  ${PROBREACH_TEST_DIR}/main_test.cpp)
target_link_libraries(formal_bad_test_3 probreach_formal -lgtest)
add_test(formal_bad_test_3 "${PROBREACH_BINARY_DIR}/test/functional/formal/formal_bad_test_3")

add_executable(formal_bad_test_4
  ${PROBREACH_TEST_DIR}/functional/formal/bad_test_4.cpp
  ${PROBREACH_TEST_DIR}/main_test.cpp)
target_link_libraries(formal_bad_test_4 probreach_formal -lgtest)
add_test(formal_bad_test_4 "${PROBREACH_BINARY_DIR}/test/functional/formal/formal_bad_test_4")

add_executable(formal_car_stopping_nonlinear_test_1
  ${PROBREACH_TEST_DIR}/functional/formal/car_stopping_nonlinear_test_1.cpp
  ${PROBREACH_TEST_DIR}/main_test.cpp)
target_link_libraries(formal_car_stopping_nonlinear_test_1 probreach_formal -lgtest)
add_test(formal_car_stopping_nonlinear_test_1 "${PROBREACH_BINARY_DIR}/test/functional/formal/formal_car_stopping_nonlinear_test_1")
