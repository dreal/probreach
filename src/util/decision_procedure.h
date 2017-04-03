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

    int evaluate_complement(vector<pdrh::mode*>, vector<box>, string, string);
    int evaluate_complement(vector<pdrh::mode*>, vector<box>, string);

    // evaluate a set of boxes using iSAT
    int evaluate_isat(vector<box>);

    int evaluate_isat(string, vector<box>);

    int synthesize(pdrh::state, vector<pdrh::mode*>, box, int, box);
    int synthesize(pdrh::state, pdrh::state, vector<pdrh::mode*>, box);

    // evaluating all paths
    int evaluate(vector<vector<pdrh::mode*>>, vector<box>, string);
}

#endif //PROBREACH_DECISION_PROCEDURE_H
