//
// Created by fedor on 29/12/15.
//
#include <capd/capdlib.h>
#include <capd/intervals/lib.h>

#include "box.h"
#include "node.h"

#ifndef PROBREACH_BOX_FACTORY_H
#define PROBREACH_BOX_FACTORY_H

namespace box_factory
{
std::vector<box>
  cartesian_product(std::map<std::string, std::vector<capd::interval>>);
std::vector<box> bisect(box);
std::vector<box> partition(box, double);
std::vector<box> partition(box, std::map<std::string, capd::interval>);
std::vector<box> partition(box, std::map<std::string, std::string>);
std::vector<box> partition(box, int);
std::vector<box> bisect(box, std::map<std::string, capd::interval>);
std::vector<box> bisect(box, std::map<std::string, std::string>);
std::vector<box> bisect(box, std::map<std::string, pdrh::node *>);
std::vector<box> bisect(box, std::vector<std::string>, double);
std::vector<box> bisect(box, std::vector<std::string>);
std::vector<box> merge(std::vector<box>);
box merge(box, box);
box get_mean(std::vector<box>);
box get_stddev(std::vector<box>);
box get_keys_diff(box, box);
box sqrt(box);
box log(box);
box get_cover(std::vector<box>);
bool compatible(std::vector<box>);
box map_box(box, box);
bool intersect(capd::interval, capd::interval);
box box_hull(std::vector<box>);

// checks map for intersection conflicts
// first argument the initial map
// second argument the map which is being tested
std::pair<std::map<box, capd::interval>, std::map<box, capd::interval>>
  get_intersection_conflicts(
    std::map<box, capd::interval>,
    std::map<box, capd::interval>);

// sort a vector of pairs by probability value
// first argument -- target unsorted vector
// second argument -- order (ascending in true and descending if false)
// vector<pair<box, capd::interval>> sort(vector<pair<box, capd::interval>>);
} // namespace box_factory

#endif // PROBREACH_BOX_FACTORY_H
