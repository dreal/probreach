//
// Created by fedor on 23/01/17.
//

#include <gtest/gtest.h>
#include "box_factory.h"
#include "box.h"

TEST(get_intersection_conflicts, no_conflicts)
{
  map<box, capd::interval> lhs, rhs;
  lhs.insert(make_pair(box("a:[0,1];"), capd::interval("0", "0.5")));
  lhs.insert(make_pair(box("a:[1,2];"), capd::interval("0.25", "0.75")));
  lhs.insert(make_pair(box("a:[2,3];"), capd::interval("0.5", "1")));

  rhs.insert(make_pair(box("a:[0,0.5];"), capd::interval("0", "0.5")));
  rhs.insert(make_pair(box("a:[0.5,1];"), capd::interval("0", "0.5")));
  rhs.insert(make_pair(box("a:[1,1.5];"), capd::interval("0.25", "0.75")));
  rhs.insert(make_pair(box("a:[1.5,2];"), capd::interval("0.25", "0.75")));
  rhs.insert(make_pair(box("a:[2,2.5];"), capd::interval("0.5", "1")));
  rhs.insert(make_pair(box("a:[2.5,3];"), capd::interval("0.5", "1")));

  pair<map<box, capd::interval>, map<box, capd::interval>> conflicts;
  conflicts = box_factory::get_intersection_conflicts(lhs, rhs);
  EXPECT_TRUE(conflicts.first.empty() && conflicts.second.empty());

  conflicts = box_factory::get_intersection_conflicts(rhs, lhs);
  EXPECT_TRUE(conflicts.first.empty() && conflicts.second.empty());

  rhs.clear();
  rhs.insert(make_pair(box("a:[0.78,0.78];"), capd::interval("0.12", "0.22")));
  conflicts = box_factory::get_intersection_conflicts(lhs, rhs);
  EXPECT_TRUE(conflicts.first.empty() && conflicts.second.empty());

  conflicts = box_factory::get_intersection_conflicts(rhs, lhs);
  EXPECT_TRUE(conflicts.second.empty());
}

TEST(get_intersection_conflicts, probability_conflict)
{
  map<box, capd::interval> lhs, rhs;
  lhs.insert(make_pair(box("a:[0,1];"), capd::interval("0", "0.5")));
  lhs.insert(make_pair(box("a:[1,2];"), capd::interval("0.25", "0.75")));
  lhs.insert(make_pair(box("a:[2,3];"), capd::interval("0.5", "1")));

  rhs.insert(make_pair(box("a:[0.78,0.78];"), capd::interval("0.65", "0.75")));
  pair<map<box, capd::interval>, map<box, capd::interval>> conflicts =
    box_factory::get_intersection_conflicts(lhs, rhs);
  EXPECT_TRUE(!conflicts.first.empty() && !conflicts.second.empty());
}

TEST(get_intersection_conflicts, box_conflict)
{
  map<box, capd::interval> lhs, rhs;
  lhs.insert(make_pair(box("a:[0,1];"), capd::interval("0", "0.5")));
  lhs.insert(make_pair(box("a:[1,2];"), capd::interval("0.25", "0.75")));
  lhs.insert(make_pair(box("a:[2,3];"), capd::interval("0.5", "1")));

  rhs.insert(make_pair(box("a:[-0.1,-0.1];"), capd::interval("0.12", "0.22")));
  pair<map<box, capd::interval>, map<box, capd::interval>> conflicts =
    box_factory::get_intersection_conflicts(lhs, rhs);
  EXPECT_TRUE(!conflicts.first.empty());
}
