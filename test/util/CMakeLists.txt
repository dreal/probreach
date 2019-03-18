if(GTEST_FOUND)
    # Building tests
    enable_testing()

    include_directories("${PROBREACH_SOURCE_DIR}/util")

    # setting the output directory for ProbReach
    set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${PROBREACH_BINARY_DIR}/test)

    # unit test for box.cpp
    add_executable(box_test ${PROBREACH_TEST_DIR}/util/box_test.cpp
            ${PROBREACH_TEST_DIR}/main_test.cpp
            ${PROBREACH_SOURCE_DIR}/util/box.cpp)
    target_link_libraries(box_test ${CAPD_LIBRARIES} -lgtest)
    add_test(box_test ${PROBREACH_BINARY_DIR}/test/util/box_test)

    # unit test for the methods in node.cpp
    add_executable(node_test ${PROBREACH_TEST_DIR}/util/node_test.cpp
            ${PROBREACH_TEST_DIR}/main_test.cpp
            ${PROBREACH_SOURCE_DIR}/util/node.cpp)
    target_link_libraries(node_test -lgtest)
    add_test(node_test ${PROBREACH_BINARY_DIR}/test/util/node_test)

#    # unit test for the methods in naive.cpp
#    add_executable(naive_test ${PROBREACH_TEST_DIR}/util/naive_test.cpp
#            ${PROBREACH_TEST_DIR}/main_test.cpp
#            ${PROBREACH_SOURCE_DIR}/util/node.cpp
#            ${PROBREACH_SOURCE_DIR}/util/naive.cpp)
#    target_link_libraries(naive_test -lgtest)
#    add_test(naive_test ${PROBREACH_BINARY_DIR}/test/util/naive_test)

    # unit test for stability.cpp
#    add_executable(stability_test ${PROBREACH_TEST_DIR}/util/stability_test.cpp
#            ${PROBREACH_TEST_DIR}/main_test.cpp
#            ${PROBREACH_SOURCE_DIR}/util/stability.cpp)
#    target_link_libraries(stability_test ${DREAL_LIBRARIES} -lgtest)
#    add_test(stability_test ${PROBREACH_BINARY_DIR}/test/stability_test)

    # unit test for box_factory.cpp
#    add_executable(box_factory_test ${PROBREACH_TEST_DIR}/util/box_factory_test.cpp
#            ${PROBREACH_TEST_DIR}/main_test.cpp
#            ${PROBREACH_SOURCE_DIR}/util/box.cpp
#            ${PROBREACH_SOURCE_DIR}/util/box_factory.cpp)
#    target_link_libraries(box_test ${DREAL_LIBRARIES} -lgtest)
#    add_test(box_factory_test ${PROBREACH_BINARY_DIR}/test/box_factory_test)

#    # unit test for node.cpp
#    add_executable(node_test ${PROBREACH_TEST_DIR}/pdrh2smt/node_test.cpp
#            ${PROBREACH_TEST_DIR}/main_test.cpp
#            ${PROBREACH_SOURCE_DIR}/pdrh2smt/node.cpp)
#    target_link_libraries(node_test ${DREAL_LIBRARIES} -lgtest)
#    add_test(node_test ${PROBREACH_BINARY_DIR}/test/node_test)
#
#    # unit test for pdrhparser.cpp
#    add_executable(pdrhparser_test ${PROBREACH_TEST_DIR}/pdrh2smt/parser/pdrhparser_test.cpp
#            ${PROBREACH_TEST_DIR}/main_test.cpp)
#    target_link_libraries(pdrhparser_test ${DREAL_LIBRARIES} -lgtest -lfl pdrh2smt)
#    add_test(pdrhparser_test ${PROBREACH_BINARY_DIR}/test/pdrhparser_test)
#
#    # unit test for isat_generator.cpp
#    add_executable(isat_generator_test ${PROBREACH_TEST_DIR}/pdrh2smt/isat_generator_test.cpp
#            ${PROBREACH_TEST_DIR}/main_test.cpp
#            ${PROBREACH_SOURCE_DIR}/pdrh2smt/isat_generator.cpp)
#    target_link_libraries(isat_generator_test ${DREAL_LIBRARIES} -lgtest -lfl pdrh2smt)
#    add_test(isat_generator_test ${PROBREACH_BINARY_DIR}/test/isat_generator_test)

    # unit test for solver_wrapper.cpp
#    add_executable(solver_wrapper_test ${PROBREACH_TEST_DIR}/solver/solver_wrapper_test.cpp
#            ${PROBREACH_TEST_DIR}/main_test.cpp
#            ${PROBREACH_SOURCE_DIR}/solver/solver_wrapper.cpp
#            ${PROBREACH_SOURCE_DIR}/solver/isat_wrapper.cpp
#            ${PROBREACH_SOURCE_DIR}/solver/dreal_wrapper.cpp)
#    target_link_libraries(solver_wrapper_test ${DREAL_LIBRARIES} -lgtest -lfl pdrh2smt)
#    add_test(solver_wrapper_test ${PROBREACH_BINARY_DIR}/test/solver_wrapper_test)

endif(GTEST_FOUND)
