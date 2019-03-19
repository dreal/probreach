//
// Created by fedor on 12/02/19.
//

#ifndef PROBREACH_FORMAL_H
#define PROBREACH_FORMAL_H

#include <capd/intervals/lib.h>

namespace formal
{
    // evaluating reachability in hybrid automata (arg1: min depth, arg2: max depth)
    int evaluate_ha(int, int);
    // evaluating reachability in probabilitic hybrid automata (arg1: min depth, arg2: max depth)
    capd::interval evaluate_pha(int, int);
    // evaluating reachability in nondeterministic probabilistic hybrid automata l(arg1: min depth, arg2: max depth)
    map<box, capd::interval> evaluate_npha(int, int);
    // performing parameter synthesis (arg: time series data). return: vectors of sat, undet and unsat boxes
    tuple<vector<box>, vector<box>, vector<box>> evaluate_psy(map<string, vector<pair<pdrh::node*, pdrh::node*>>>);
}


#endif //PROBREACH_FORMAL_H
