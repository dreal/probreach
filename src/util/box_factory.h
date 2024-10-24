//
// Created by fedor on 29/12/15.
//
#include <capd/capdlib.h>
#include <capd/intervals/lib.h>

#include "box.h"
#include "node.h"

#ifndef PROBREACH_BOX_FACTORY_H
#define PROBREACH_BOX_FACTORY_H

class box_factory
{
public:
  static std::vector<box>
    cartesian_product(std::map<std::string, std::vector<capd::interval>>);
  static std::vector<box> bisect(box);
  static std::vector<box> partition(box, double);
  static std::vector<box> partition(box, std::map<std::string, capd::interval>);
  static std::vector<box> partition(box, std::map<std::string, std::string>);
  static std::vector<box> partition(box, int);
  static std::vector<box> bisect(box, std::map<std::string, capd::interval>);
  static std::vector<box> bisect(box, std::map<std::string, std::string>);
  static std::vector<box> bisect(box, std::map<std::string, pdrh::node *>);
  static std::vector<box> bisect(box, std::vector<std::string>, double);
  static std::vector<box> bisect(box, std::vector<std::string>);
  static std::vector<box> merge(std::vector<box>);
  static box merge(box, box);
  static box get_mean(std::vector<box>);
  static box get_stddev(std::vector<box>);
  static box get_keys_diff(box, box);
  static box get_cover(std::vector<box>);
  static bool compatible(std::vector<box>);
  static box map_box(box, box);
  static bool intersect(capd::interval, capd::interval);
  static box box_hull(std::vector<box>);

  // checks map for intersection conflicts
  // first argument the initial map
  // second argument the map which is being tested
  static std::pair<std::map<box, capd::interval>, std::map<box, capd::interval>>
    get_intersection_conflicts(
      std::map<box, capd::interval>,
      std::map<box, capd::interval>);

  // sort a vector of pairs by probability value
  // first argument -- target unsorted vector
  // second argument -- order (ascending in true and descending if false)
  // vector<pair<box, capd::interval>> sort(vector<pair<box, capd::interval>>);
};

#endif // PROBREACH_BOX_FACTORY_H
