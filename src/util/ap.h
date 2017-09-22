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
#include "pdrh.h"

using namespace std;

namespace ap
{

    extern pdrh::type model_type;
    extern pair<pdrh::node*, pdrh::node*> time;
    extern map<string, tuple<pdrh::node*, pdrh::node*, pdrh::node*, pdrh::node*>> rv_map;
    extern map<string, string> rv_type_map;
    extern map<string, map<pdrh::node*, pdrh::node*>> dd_map;
    extern map<string, pair<pdrh::node*, pdrh::node*>> var_map;
    extern map<string, pair<pdrh::node*, pdrh::node*>> par_map;
    extern map<string, pdrh::node*> syn_map;
    extern vector<pdrh::mode> modes;
    extern vector<pdrh::state> init;
    extern vector<pdrh::state> goal;
    extern vector<vector<pdrh::mode*>> paths;

    namespace distribution
    {
        extern map<string, pair<pdrh::node*, pdrh::node*>> uniform;
        extern map<string, pair<pdrh::node*, pdrh::node*>> normal;
        extern map<string, pdrh::node*> exp;
        extern map<string, pair<pdrh::node*, pdrh::node*>> gamma;
    }

    void copy_model();
    void modify_model();
    void revert_model();

}

#endif //PROBREACH_AP_H
