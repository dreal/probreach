//
// Created by fedor on 04/04/16.
//

#ifndef PROBREACH_RANDOM_H
#define PROBREACH_RANDOM_H

#include<box.h>
#include <gsl/gsl_rng.h>
#include <gsl/gsl_qrng.h>

namespace rnd
{
    box get_random_sample(gsl_rng*);
    box get_sobol_sample(gsl_qrng*, box);
    // the first argument is a random number generator,
    // the second argument is the mean vector
    // the third argument is the standard deviation vector
    box get_normal_random_sample(gsl_rng*, box, box);
}

#endif //PROBREACH_RANDOM_H
