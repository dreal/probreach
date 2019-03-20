//
// Created by fedor on 26/02/16.
//

#ifndef PROBREACH_DECISION_PROCEDURE_H
#define PROBREACH_DECISION_PROCEDURE_H
#include<iostream>
#include "model.h"
#include "box.h"

using namespace std;

namespace decision_procedure
{
    enum result {SAT, UNSAT, UNDET, ERROR};

    // used for formal verification
    int evaluate(vector<pdrh::mode *>, vector<box>, string, string);

    // evaluating all paths
    int evaluate(vector<vector<pdrh::mode *>>, vector<box>, string, string);

    // first argument is the path to be evaluated,
    // second argument is the set of nondet boxes
    // third argument is the path to the solver binary
    // fourt argument is the string of solver options
    int evaluate_delta_sat(vector<pdrh::mode*>, vector<box>, string, string);

    // first argument is the path to be evaluated,
    // second argument is the set of nondet boxes
    // third argument is the path to the solver binary
    // fourt argument is the string of solver options
    int evaluate_complement(vector<pdrh::mode*>, vector<box>, string, string);

    // first argument contains the odes to compute and the invariants to check
    // second argument is the time horizon for ode integration
    // third argument is the interval initial condition for the ode system
    int check_invariants(pdrh::mode*, capd::interval, box, vector<box>, string, string);

    // first argument is the mode
    // second argument is the initial condition
    // third argument is parameter values
    std::pair<capd::interval, box> get_jump_time(pdrh::mode*, pdrh::mode::jump, box, vector<box>);

}

#endif //PROBREACH_DECISION_PROCEDURE_H
