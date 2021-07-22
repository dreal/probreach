//
// Created by fedor on 03/03/17.
//

#ifndef PROBREACH_ISAT_WRAPPER_H
#define PROBREACH_ISAT_WRAPPER_H

#include "solver_wrapper.h"

namespace isat
{

    // Evaluates an iSAT model file specified by the second argument
    // using the executable defined by the first parameter
    // with command line arguments defined by the third parameter
    solver::output evaluate(std::string, std::string, std::string);

}

#endif //PROBREACH_ISAT_WRAPPER_H

