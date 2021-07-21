//
// Created by fedor on 06/11/17.
//

#ifndef PROBREACH_SMT2_GENERATOR_H
#define PROBREACH_SMT2_GENERATOR_H

#include <capd/capdlib.h>

#include <iostream>

#include "box.h"
#include "model.h"

namespace smt2_generator {

// generates the formula for the invariants check
// first argument contains the odes to compute and the invariants to check
// second arguments is the time horizon for ode integration
// third argument is the interval initial condition for the ode system
// fourth argument is the vector of samples
std::string generate_flow_invt_check(pdrh::mode*, capd::interval, box,
                                     vector<box>);

// generates the complement formula for the invariants check
// first argument contains the odes to compute and the invariants to check
// second arguments is the time horizon for ode integration
// third argument is the interval initial condition for the ode system
// fourth argument is the vector of samples
std::string generate_flow_invt_check_c(pdrh::mode*, capd::interval, box,
                                       vector<box>);

// generates the formula to check the jumps
// first argument contains the odes to compute and the jumps to check
// second argument is the interval initial condition for the ode system
// third argument is the vector of samples
std::string generate_jump_check(pdrh::mode*, vector<pdrh::mode::jump>, box,
                                vector<box>);

// generates reachability formulas
std::string reach_to_smt2(std::vector<pdrh::mode*>, std::vector<box>);
std::string reach_c_to_smt2(std::vector<pdrh::mode*>, std::vector<box>);
std::string reach_c_to_smt2(int, std::vector<pdrh::mode*>, vector<box>);

}  // namespace smt2_generator

#endif  // PROBREACH_SMT2_GENERATOR_H
