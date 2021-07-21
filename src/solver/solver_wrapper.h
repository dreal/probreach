//
// Created by fedor on 02/03/17.
//

#ifndef PROBREACH_SOLVER_WRAPPER_H
#define PROBREACH_SOLVER_WRAPPER_H

#include <iostream>

using namespace std;

namespace solver {
enum type { ISAT, DREAL, UNKNOWN_SOLVER };

enum output { SAT, UNSAT };

// Detects a type of the solver given a full
// path to the binary
type detect_solver(string);

// Evaluates a formula specified by the second argument, using a binary
// specified in the first argument with command line arguments
// defined by the third argument. The last argument specifies the type
// of the solver
output evaluate(string, string, string, type);

}  // namespace solver

#endif  // PROBREACH_SOLVER_WRAPPER_H
