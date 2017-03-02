//
// Created by fedor on 02/03/17.
//

#ifndef PROBREACH_SOLVER_WRAPPER_H
#define PROBREACH_SOLVER_WRAPPER_H

#include<iostream>

using namespace std;

namespace solver
{
    enum type {ISAT, DREAL, UNKNOWN_SOLVER};

    // detects a type of the solver given a full
    // path to the binary
    type detect_solver(string);
}

#endif //PROBREACH_SOLVER_WRAPPER_H
