//
// Created by fedor on 26/02/16.
//

#ifndef PROBREACH_DECISION_PROCEDURE_H
#define PROBREACH_DECISION_PROCEDURE_H
#include<iostream>
#include "model.h"

using namespace std;

namespace decision_procedure
{
    enum result {SAT, UNSAT, UNDET, ERROR, SOLVER_TIMEOUT, SOLVER_PROCESS_ERROR};
    int evaluate(vector<pdrh::mode*>, vector<box>);
    int evaluate(vector<box>, int, string);
    int evaluate(vector<pdrh::mode*>, vector<box>, string);
    //int evaluate(std::vector<pdrh::mode*>, rv_box*, dd_box*, nd_box*);
    int evaluate(pdrh::state, pdrh::state, vector<pdrh::mode*>, vector<box>);
    int evaluate_delta_sat(vector<pdrh::mode*>, vector<box>);

    int synthesize(pdrh::state, vector<pdrh::mode*>, box, int, box);
    int synthesize(pdrh::state, pdrh::state, vector<pdrh::mode*>, box);
}

#endif //PROBREACH_DECISION_PROCEDURE_H
