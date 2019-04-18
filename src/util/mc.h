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
    capd::interval evaluate_pha_chernoff(int, int, double, double, vector<box>);
    capd::interval evaluate_pha_bayesian(int, int, double, double, vector<box>);

    // the last argument is the sample size for cross entropy method
//    pair<box, capd::interval> evaluate_npha_sobol(int, int, int);
    pair<box, capd::interval> evaluate_npha_cross_entropy_normal(size_t, size_t, size_t, size_t, double, double);
//    pair<box, capd::interval> evaluate_npha_cross_entropy_beta(int, int, int);

}

#endif //PROBREACH_ALGORITHM_H
