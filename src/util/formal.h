//
// Created by fedor on 12/02/19.
//

#ifndef PROBREACH_FORMAL_H
#define PROBREACH_FORMAL_H

#include <capd/intervals/lib.h>

#include "box.h"

namespace formal
{
// evaluating reachability in a hybrid automata
// arg1: min depth,
// arg2: max depth
int evaluate_ha(int, int);

// evaluating the reachability probability in a probabilitic hybrid automata
// arg1: min depth,
// arg2: max depth
capd::interval evaluate_pha(int, int);

// evaluating the upper bound of the reachability probability
// arg1: min depth,
// arg2: max depth
capd::interval evaluate_pha_upper_bound(int, int);

// evaluating the reachability probability in
// a nondeterministic probabilistic hybrid automata
// arg1: min depth,
// arg2: max depth
std::map<box, capd::interval> evaluate_npha(int, int);

// evaluating the upper bound of the reachability probability in
// a nondeterministic probabilistic hybrid automata
// arg1: min depth,
// arg2: max depth
std::map<box, capd::interval> evaluate_npha_upper_bound(int, int);
} // namespace formal

#endif // PROBREACH_FORMAL_H
