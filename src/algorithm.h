//
// Created by fedor on 03/03/16.
//

#ifndef PROBREACH_ALGORITHM_H
#define PROBREACH_ALGORITHM_H

#include <capd/intervals/lib.h>
#include "decision_procedure.h"

namespace algorithm
{
    decision_procedure::result evaluate_ha(int);
    decision_procedure::result evaluate_ha(int, int);
    //capd::interval evaluate_pha();
}

#endif //PROBREACH_ALGORITHM_H
