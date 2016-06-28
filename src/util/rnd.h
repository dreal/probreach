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
    box get_quasi_random_sample(gsl_qrng*);
}

#endif //PROBREACH_RANDOM_H
