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
    // method to implement
    capd::interval evaluate_pha_qmc(int);
}
#endif //PROBREACH_QMC_H
