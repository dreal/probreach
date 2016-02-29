//
// Created by fedor on 26/02/16.
//

#ifndef PROBREACH_DECISION_PROCEDURE_H
#define PROBREACH_DECISION_PROCEDURE_H
#include<iostream>
#include "model.h"

namespace decision_procedure
{
    enum result {SAT, UNSAT, UNDET, ERROR};
    int evaluate(std::vector<pdrh::mode*>, std::vector<box>);
    int evaluate(std::vector<pdrh::mode*>, rv_box*, dd_box*, nd_box*);
}

#endif //PROBREACH_DECISION_PROCEDURE_H
