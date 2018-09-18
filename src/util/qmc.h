//
// Created by mariia on 10/09/18.
//

#ifndef PROBREACH_QMC_H
#define PROBREACH_QMC_H

#include <capd/intervals/lib.h>
#include "decision_procedure.h"

using namespace std;

namespace algorithm
{
    // evaluating probability using simple ICDF QMC algorithm
    capd::interval evaluate_qmc();
    // evaluating CI using RQMC CLT algorithm
    capd::interval evaluate_rqmc_CLT();
    // evaluating CI using RQMC Agresti-Coull algorithm
    capd::interval evaluate_rqmc_AC();
    // evaluating CI using RQMC Willson algorithm
    capd::interval evaluate_rqmc_Will();
    // evaluating CI using RQMC Logit algorithm
    capd::interval evaluate_rqmc_Log();
    // evaluating CI using RQMC Anscombe algorithm
    capd::interval evaluate_rqmc_Ans();
    // evaluating CI using RQMC Arcsine algorithm
    capd::interval evaluate_rqmc_Arc();
    // evaluating CI using Qint algorithm
    capd::interval evaluate_Qint();
    // evaluating CI using all CI algorithms
    capd::interval C();
}
#endif //PROBREACH_QMC_H
