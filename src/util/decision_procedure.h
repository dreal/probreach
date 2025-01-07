//
// Created by fedor on 26/02/16.
//

#ifndef PROBREACH_DECISION_PROCEDURE_H
#define PROBREACH_DECISION_PROCEDURE_H
#include <iostream>
#include "model.h"
#include "box.h"

namespace decision_procedure
{
enum result
{
  SAT,
  UNSAT,
  UNDET,
  ERROR
};

// evaluating all paths
int evaluate(
  std::vector<std::vector<pdrh::mode *>>,
  std::vector<box>,
  std::string,
  std::string);

// evaluates a path
int evaluate(
  std::vector<pdrh::mode *>,
  std::vector<box>,
  std::string,
  std::string);

// first argument is the path to be evaluated,
// second argument is the set of nondet boxes
// third argument is the path to the solver binary
// fourt argument is the string of solver options
int evaluate_delta_sat(
  std::vector<pdrh::mode *>,
  std::vector<box>,
  std::string,
  std::string);

// first argument is the path to be evaluated,
// second argument is the set of nondet boxes
// third argument is the path to the solver binary
// fourt argument is the string of solver options
int evaluate_delta_sat(
  std::vector<std::vector<pdrh::mode *>>,
  std::vector<box>,
  std::string,
  std::string);

// first argument is the path to be evaluated,
// second argument is the set of nondet boxes
// third argument is the path to the solver binary
// fourt argument is the string of solver options
int evaluate_complement(
  std::vector<pdrh::mode *>,
  std::vector<box>,
  std::string,
  std::string);

// first argument contains the odes to compute and the invariants to check
// second argument is the time horizon for ode integration
// third argument is the interval initial condition for the ode system
int check_invariants(
  pdrh::mode *,
  capd::interval,
  box,
  std::vector<box>,
  std::string,
  std::string);

// first argument is the mode
// second argument is the initial condition
// third argument is parameter values
std::pair<capd::interval, box>
get_jump_time(pdrh::mode *, pdrh::mode::jump, box, std::vector<box>);

} // namespace decision_procedure

#endif //PROBREACH_DECISION_PROCEDURE_H
