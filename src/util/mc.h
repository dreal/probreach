//
// Created by fedor on 03/03/16.
//

#ifndef PROBREACH_ALGORITHM_H
#define PROBREACH_ALGORITHM_H

#include <capd/intervals/lib.h>
#include "decision_procedure.h"

using namespace std;

namespace algorithm
{
    // evaluating reachability in probabilitic hybrid automata by sampling (arg1: min depth, arg2: max depth, arg3: sample size)
    capd::interval evaluate_pha_chernoff(int, int, double, double);
    // evaluating reachability in probabilitic hybrid automata by sampling (arg1: min depth, arg2: max depth, arg3: sample size)
    capd::interval evaluate_pha_chernoff_delta_sat(int, int, double, double);
    capd::interval evaluate_pha_bayesian_delta_sat(int, int, double, double);
    capd::interval evaluate_pha_bayesian(int, int, double, double);
    long int get_cernoff_bound(double, double);

    capd::interval evaluate_pha_chernoff(int, int, double, double, vector<box>);
    capd::interval evaluate_pha_bayesian(int, int, double, double, vector<box>);

    // the last argument is the sample size for cross entropy method
    pair<box, capd::interval> evaluate_npha_sobol(int, int, int);
    pair<box, capd::interval> evaluate_npha_cross_entropy_normal(size_t, size_t, size_t, size_t, double, double);
    pair<box, capd::interval> evaluate_npha_cross_entropy_beta(int, int, int);

    pair<capd::interval, box> solve_min_max();
    capd::interval compute_robustness();

}

#endif //PROBREACH_ALGORITHM_H
