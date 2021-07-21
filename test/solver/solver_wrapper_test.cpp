//
// Created by fedor on 02/03/17.
//

#include "solver_wrapper.h"

#include <gtest/gtest.h>

#include <fstream>

#include "box.h"
#include "isat_generator.h"
#include "model.h"
#include "node.h"

using namespace std;

TEST(detect_solver, normal) {
  EXPECT_EQ(solver::detect_solver("/home/fedor/probreach/bin/dReal"),
            solver::DREAL);
  EXPECT_EQ(solver::detect_solver("/home/fedor/probreach/bin/isat-ode"),
            solver::ISAT);
  EXPECT_EQ(solver::detect_solver("/home/fedor/probreach/bin/ProbReach"),
            solver::UNKNOWN_SOLVER);
  EXPECT_THROW(solver::detect_solver("/home/fedor/dreal3/bin/dReach"),
               runtime_error);
}

TEST(isat_wrapper, normal) {
  string pdrh_filename("/home/fedor/isat/model/cars/stop-nonlinear.pdrh");
  model m = parse_pdrh(pdrh_filename);
  // generating isat model
  string isat_model = isat_generator::generate_isat_model(m);
  // cout << isat_model << endl;
  string isat_filename(pdrh_filename + ".hys");
  ofstream out(isat_filename);
  out << isat_model;
  out.close();
  string isat_path("/home/fedor/isat/isat-ode");
  string isat_args(
      "--verify-sol --start-depth 7 --max-depth 7 "
      "--ode-opts=--continue-after-not-reaching-horizon "
      "--ode-opts=--detect-independent-ode-groups");
  solver::output res =
      solver::evaluate(isat_path, isat_filename, isat_args, solver::type::ISAT);
  EXPECT_EQ(res, solver::output::SAT);
  // changing model's goal
  m.remove_goals();
  node goal(">=", vector<node>{node("s"), node("400")});
  m.push_goal(4, goal);
  isat_model = isat_generator::generate_isat_model(m);
  // cout << isat_model << endl;
  ofstream out2(isat_filename);
  out2 << isat_model;
  out2.close();
  res =
      solver::evaluate(isat_path, isat_filename, isat_args, solver::type::ISAT);
  EXPECT_EQ(res, solver::output::UNSAT);
  // insulin infusion
  pdrh_filename = "/home/fedor/isat/model/insulin-pump/insulin-pump.pdrh";
  isat_filename = pdrh_filename + ".hys";
  isat_args =
      "--verify-sol --start-depth 3 --max-depth 3 "
      "--ode-opts=--continue-after-not-reaching-horizon "
      "--ode-opts=--detect-independent-ode-groups";
  m = parse_pdrh(pdrh_filename);
  // cout << m << endl;
  isat_model = isat_generator::generate_isat_model(m);
  ofstream out3(isat_filename);
  out3 << isat_model;
  out3.close();
  res =
      solver::evaluate(isat_path, isat_filename, isat_args, solver::type::ISAT);
  EXPECT_EQ(res, solver::output::SAT);
}