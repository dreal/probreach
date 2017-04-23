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
    // evaluating reachability in hybrid automata (arg: depth)
    //decision_procedure::result evaluate_ha(int);
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
    map<box, capd::interval> evaluate_npha(int);
    // evaluating reachability in nondeterministic probabilistic hybrid automata l(arg1: min depth, arg2: max depth)
    map<box, capd::interval> evaluate_npha(int, int);
    // evaluating reachability in nondeterministic hybrid automata (arg: depth)
    map<box, decision_procedure::result> evaluate_nha(int);
    // evaluating reachability in nondeterministic hybrid automata (arg1: min depth, arg2: max depth)
    map<box, decision_procedure::result> evaluate_nha(int, int);
    // performing parameter synthesis (arg: time series data). return: vectors of sat, undet and unsat boxes
    tuple<vector<box>, vector<box>, vector<box>> evaluate_psy(map<string, vector<pair<pdrh::node*, pdrh::node*>>>);
    capd::interval evaluate_pha_bayesian_delta_sat(int, int, double, double);
    capd::interval evaluate_pha_bayesian(int, int, double, double);
    long int get_cernoff_bound(double, double);

    capd::interval evaluate_pha_chernoff(int, int, double, double, vector<box>);
    capd::interval evaluate_pha_bayesian(int, int, double, double, vector<box>);

    // the last argument is the sample size for cross entropy method
    pair<box, capd::interval> evaluate_npha_sobol(int, int, int);
    pair<box, capd::interval> evaluate_npha_cross_entropy_normal(int, int, int);
    pair<box, capd::interval> evaluate_npha_cross_entropy_beta(int, int, int);

}

#endif //PROBREACH_ALGORITHM_H
