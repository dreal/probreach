//
// Created by fedor on 12/06/18.
//

#ifndef PROBREACH_PDRH2BOX_H
#define PROBREACH_PDRH2BOX_H

#include <iostream>
#include <vector>
#include <capd/capdlib.h>
#include <capd/intervals/lib.h>
#include <tuple>
#include "box.h"
#include "node.h"

namespace pdrh2box
{
    capd::interval node_to_interval(pdrh::node*);
    capd::interval node_to_interval(pdrh::node*, std::vector<box>);
    bool node_to_boolean(pdrh::node*, std::vector<box>);
    pdrh::node* box_to_node(box);
    bool check_zero_crossing(pdrh::node*, std::vector<box>, box, box);

//    box node_to_box(pdrh::node*);

    box get_nondet_domain();
    box get_domain();
    box get_psy_domain();

    box init_to_box(vector<box>);
}
#endif //PROBREACH_PDRH2BOX_H
