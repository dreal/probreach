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
    box merge(box, box);
    box get_mean(vector<box>);
    box get_stddev(vector<box>);
    box get_keys_diff(box, box);
    box sqrt(box);
    box get_cover(vector<box>);

    // sort a vector of pairs by probability value
    // first argument -- target unsorted vector
    // second argument -- order (ascending in true and descending if false)
    //vector<pair<box, capd::interval>> sort(vector<pair<box, capd::interval>>);
}

#endif //PROBREACH_BOX_FACTORY_H
