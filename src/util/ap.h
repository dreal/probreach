//
// Created by fedor on 22/09/17.
//

#ifndef PROBREACH_AP_H
#define PROBREACH_AP_H

#include <iostream>
#include <vector>
#include <map>
#include <capd/capdlib.h>
#include <capd/intervals/lib.h>
#include <tuple>
#include "box.h"
#include "model.h"

using namespace std;

namespace ap
{
    extern vector<box> unsat_samples;

//    void get_first_time_node(pdrh::node*, pdrh::node*);
//    pdrh::node* get_time_node_neg(pdrh::node*);

    capd::interval get_sample_rate(pdrh::node*);
    capd::interval get_sample_rate(pdrh::mode*);

    capd::interval get_meal_time(pdrh::node*, vector<box>);
    capd::interval get_meal_time(pdrh::mode*, vector<box>);

    int jumps_per_mode(pdrh::mode*, vector<box>);

    // current and previous mode
    int jumps_per_mode(pdrh::mode*, pdrh::mode*, vector<box>);

    bool accept_path(vector<pdrh::mode*>, vector<box>);
    vector<vector<pdrh::mode*>> get_all_paths(vector<box>);

//    box init_to_box(vector<box>);

    box solve_odes(map<string, pdrh::node*>, box, capd::interval, vector<box>);
    box solve_odes_nonrig(map<string, pdrh::node*>, box, capd::interval, vector<box>);
    box solve_odes_discrete(map<string, pdrh::node*>, box, capd::interval, size_t, vector<box>);

    int simulate_path(vector<pdrh::mode*>, box, vector<box>);

    // The last argument is the list of variables defining the objective function
    box compute_objective(vector<pdrh::mode*>, box, vector<box>, vector<string>);
    capd::interval compute_robustness(vector<pdrh::mode*>, box, vector<box>);
    capd::interval compute_max_robustness(vector<vector<pdrh::mode*>>, box, vector<box>);
    capd::interval compute_min_robustness(vector<vector<pdrh::mode*>>, box, vector<box>);

    bool check_invariants(pdrh::mode*, box, vector<box>);

    int verify(size_t, size_t, vector<box>);
    int simulate(size_t, size_t, vector<box>);

    bool is_sample_jump(pdrh::mode::jump);
    box apply_reset(map<string, pdrh::node*>, box, vector<box>);


}

#endif //PROBREACH_AP_H
