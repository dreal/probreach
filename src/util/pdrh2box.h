//
// Created by fedor on 12/06/18.
//

#ifndef PROBREACH_PDRH2BOX_H
#define PROBREACH_PDRH2BOX_H

#include <iostream>
#include <vector>
#include <map>
#include <capd/capdlib.h>
#include <capd/intervals/lib.h>
#include <tuple>
#include <box.h>
#include "model.h"

namespace pdrh2box
{
    capd::interval node_to_interval(pdrh::node*);
    capd::interval node_to_interval(pdrh::node*, vector<box>);
    bool node_to_boolean(pdrh::node*, vector<box>);
    pdrh::node* box_to_node(box);
    bool check_zero_crossing(pdrh::node*, vector<box>, box, box);

    box get_nondet_domain();
    box get_domain();
    box get_psy_domain();

    // here only one initial mode and one goal mode
    std::string reach_to_smt2(std::vector<pdrh::mode*>, std::vector<box>);
    std::string reach_c_to_smt2(std::vector<pdrh::mode*>, std::vector<box>);
    std::string reach_c_to_smt2(int, std::vector<pdrh::mode*>, vector<box>);

//    std::string reach_to_smt2(pdrh::state, pdrh::state, std::vector<pdrh::mode*>, vector<box>);
//    std::string reach_c_to_smt2(pdrh::state, pdrh::state, std::vector<pdrh::mode*>, vector<box>);
//    std::string reach_c_to_smt2(pdrh::state, pdrh::state, int, std::vector<pdrh::mode*>, std::vector<box>);
//    std::string reach_to_isat(std::vector<box>);
//    std::string reach_to_smt2_all_paths(std::vector<box>);
//    std::string reach_c_to_smt2_all_paths();
}
#endif //PROBREACH_PDRH2BOX_H
