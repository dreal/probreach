//
// Created by fedor on 04/04/16.
//

#ifndef PROBREACH_RANDOM_H
#define PROBREACH_RANDOM_H

#include<box.h>
#include <gsl/gsl_rng.h>

namespace rnd
{
    box get_sample(gsl_rng*);
}

#endif //PROBREACH_RANDOM_H
