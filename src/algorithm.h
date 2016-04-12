//
// Created by fedor on 03/03/16.
//

#ifndef PROBREACH_ALGORITHM_H
#define PROBREACH_ALGORITHM_H

#include <capd/intervals/lib.h>
#include "decision_procedure.h"

namespace algorithm
{
    // evaluating reachability in hybrid automata (arg: depth)
    decision_procedure::result evaluate_ha(int);
    // evaluating reachability in hybrid automata (arg1: min depth, arg2: max depth)
    decision_procedure::result evaluate_ha(int, int);
    // evaluating reachability in probabilitic hybrid automata (arg: depth)
    capd::interval evaluate_pha(int);
    // evaluating reachability in probabilitic hybrid automata (arg1: min depth, arg2: max depth)
    capd::interval evaluate_pha(int, int);
    // evaluating reachability in probabilitic hybrid automata by sampling (arg1: min depth, arg2: max depth, arg3: sample size)
    capd::interval evaluate_pha_chernoff(int, int, double, double);
    // evaluating reachability in probabilitic hybrid automata by sampling (arg1: min depth, arg2: max depth, arg3: sample size)
    capd::interval evaluate_pha_chernoff_delta_sat(int, int, double, double);
    // evaluating reachability in nondeterministic probabilistic hybrid automata (arg: depth)
    std::map<box, capd::interval> evaluate_npha(int);
    // evaluating reachability in nondeterministic probabilistic hybrid automata (arg1: min depth, arg2: max depth)
    std::map<box, capd::interval> evaluate_npha(int, int);
    // evaluating reachability in nondeterministic hybrid automata (arg: depth)
    std::map<box, decision_procedure::result> evaluate_nha(int);
    // evaluating reachability in nondeterministic hybrid automata (arg1: min depth, arg2: max depth)
    std::map<box, decision_procedure::result> evaluate_nha(int, int);
    // performing parameter synthesis (arg: time series data). return: vectors of sat, undet and unsat boxes
    std::tuple<std::vector<box>, std::vector<box>, std::vector<box>> evaluate_psy(std::map<std::string, std::vector<capd::interval>>);
    long int get_cernoff_bound(double, double);
}

#endif //PROBREACH_ALGORITHM_H
