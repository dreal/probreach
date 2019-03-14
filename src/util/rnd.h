//
// Created by fedor on 04/04/16.
//

#ifndef PROBREACH_RANDOM_H
#define PROBREACH_RANDOM_H

#include <box.h>
#include <gsl/gsl_rng.h>
#include <gsl/gsl_qrng.h>
#include <gsl/gsl_multiroots.h>

using namespace std;

namespace rnd
{
    box get_random_sample(gsl_rng*);
    box get_randomuni_sample(gsl_rng*); // for RQMC algorithm
    box get_sobol_sample(gsl_qrng*, box);
    box get_icdf(box);
    box get_GPicdf(box, box);
   // double find_sample_var(box b);
    // the first argument is a random number generator,
    // the second argument is the mean vector
    // the third argument is the standard deviation vector
    box get_normal_random_sample(gsl_rng*, box, box);
    box get_beta_random_sample(gsl_rng*, box, box, box);
    double digamma(double);
    int beta_system(const gsl_vector *, void *, gsl_vector *);
    struct beta_system_params
    {
        double c1;
        double c2;
    };
    pair<box, box> update_beta_dist(vector<box>, box, box, box);
    pair<double, double> solve_beta_system(double, double, double, double);
    double sobol_vector(box); //new
    double nond(box); //new
}

#endif //PROBREACH_RANDOM_H
