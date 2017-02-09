//
// Created by fedor on 08/02/17.
//

#ifndef PROBREACH_SMT2GENERATOR_H
#define PROBREACH_SMT2GENERATOR_H

#include "model.h"

namespace smt2generator
{
    // Generates a reachability formula for the shortest path
    // between one of the initial states and one of the goal states in the specified model.
    // Returns empty string if such path does not exist.
    string generate_reachability_formula(model);

    // Generates a reachability formula for the given path
    string generate_reachability_formula(model, vector<int>);

    // Generates a reachability formula for the given set of paths
    string generate_reachability_formula(model, vector<vector<int>>);

    // Generates a reachability formula for all paths of specified length
    // between the initial states and the goal states in the specified model.
    // Returns empty string if there no such paths.
    string generate_reachability_formula(model, int);

}

#endif //PROBREACH_SMT2GENERATOR_H
