//
// Created by fedor on 01/03/17.
//

#ifndef PROBREACH_ISAT_GENERATOR_CPP_H
#define PROBREACH_ISAT_GENERATOR_CPP_H

#include "model.h"

namespace isat_generator
{
    // Generates a model in iSAT-ODE format
    string generate_isat_model(model);

    // Generates a model in iSAT-ODE format for the number of transitions
    // defined by the second argument
    string generate_isat_model(model, int);
}

#endif //PROBREACH_ISAT_GENERATOR_CPP_H
