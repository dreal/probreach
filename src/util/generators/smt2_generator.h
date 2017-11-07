//
// Created by fedor on 06/11/17.
//

#ifndef PROBREACH_SMT2_GENERATOR_H
#define PROBREACH_SMT2_GENERATOR_H

#include <iostream>
#include <capd/capdlib.h>
#include "util/pdrh.h"
#include "box.h"

namespace smt2_generator
{

    // generates the formula for the invariants check
    // first argument contains the odes to compute and the invariants to check
    // second arguments is the time horizon for ode integration
    // third argument is the interval initial condition for the ode system
    // fourth argument is the vector of samples
    std::string generate_flow_invt_check(pdrh::mode*, capd::interval, box, vector<box>);

    // generates the complement formula for the invariants check
    // first argument contains the odes to compute and the invariants to check
    // second arguments is the time horizon for ode integration
    // third argument is the interval initial condition for the ode system
    // fourth argument is the vector of samples
    std::string generate_flow_invt_check_c(pdrh::mode*, capd::interval, box, vector<box>);
}

#endif //PROBREACH_SMT2_GENERATOR_H
