//
// Created by fedor on 29/12/15.
//
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include "box.h"
#include "model.h"

#ifndef PROBREACH_BOX_FACTORY_H
#define PROBREACH_BOX_FACTORY_H

using namespace std;

namespace box_factory
{
    vector<box> cartesian_product(map<string, vector<capd::interval>>);
    vector<box> bisect(box);
    vector<box> partition(box, double);
    vector<box> bisect(box, map<string, capd::interval>);
    vector<box> bisect(box, map<string, pdrh::node*>);
    vector<box> merge(std::vector<box>);
    box get_mean(box);
    box get_deviation(box);
    box merge(box, box);
}

#endif //PROBREACH_BOX_FACTORY_H
