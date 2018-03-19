//
// Created by fedor on 26/02/16.
//

#ifndef PROBREACH_DECISION_PROCEDURE_H
#define PROBREACH_DECISION_PROCEDURE_H
#include<iostream>
#include "pdrh.h"

using namespace std;

namespace decision_procedure
{
    enum result {SAT, UNSAT, UNDET, ERROR, SOLVER_TIMEOUT, SOLVER_PROCESS_ERROR};
    // used for statistical model checking
    int evaluate(vector<pdrh::mode*>, vector<box>);

    // used for formal verification
    int evaluate(vector<pdrh::mode*>, vector<box>, string);

    // used for parameter set synthesis
    int evaluate(pdrh::state, pdrh::state, vector<pdrh::mode*>, vector<box>);
    int evaluate_delta_sat(vector<pdrh::mode*>, vector<box>);
    int evaluate_delta_sat(vector<pdrh::mode*>, vector<box>, string);
    int evaluate_delta_sat(vector<pdrh::mode*>, vector<box>, string, string);
    int evaluate_flow_by_flow(vector<pdrh::mode*>, vector<box>, string, string);

    int evaluate_complement(vector<pdrh::mode*>, vector<box>, string, string);
    int evaluate_complement(vector<pdrh::mode*>, vector<box>, string);

    // evaluate a set of boxes using iSAT
    int evaluate_isat(vector<box>);
    int evaluate_isat(string, vector<box>);

    int synthesize(pdrh::state, vector<pdrh::mode*>, box, int, box);
    int synthesize(pdrh::state, pdrh::state, vector<pdrh::mode*>, box);

    // evaluating all paths
    int evaluate(vector<vector<pdrh::mode*>>, vector<box>, string);

    // first argument contains the odes to compute and the invariants to check
    // second arguments is the time horizon for ode integration
    // third argument is the interval initial condition for the ode system
    int check_invariants(pdrh::mode*, capd::interval, box, vector<box>, string, string);

    // first argument is the mode
    // second argument is the initial condition
    // third argument is parameter values
    capd::interval get_jump_time(pdrh::mode*, box, vector<box>);

    // first argument is the mode
    // second argument is the initial condition
    // third argument is parameter values
    std::pair<capd::interval, box> get_jump_time(pdrh::mode*, pdrh::mode::jump, box, vector<box>);

}

#endif //PROBREACH_DECISION_PROCEDURE_H
