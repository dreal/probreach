//
// Created by fedor on 02/03/17.
//

#include "node.h"
#include <gtest/gtest.h>
#include "model.h"
//#include "pdrhparser.hpp"
#include "solver_wrapper.h"

using namespace std;

TEST(detect_solver, normal)
{
    EXPECT_EQ(solver::detect_solver("/home/fedor/probreach/bin/dReal"), solver::DREAL);
    EXPECT_EQ(solver::detect_solver("/home/fedor/probreach/bin/isat-ode"), solver::ISAT);
    EXPECT_EQ(solver::detect_solver("/home/fedor/probreach/bin/ProbReach"), solver::UNKNOWN_SOLVER);
    EXPECT_THROW(solver::detect_solver("/home/fedor/dreal3/bin/dReach"), runtime_error);
}