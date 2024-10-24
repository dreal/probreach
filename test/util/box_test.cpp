//
// Created by fedor on 23/01/17.
//

#include <gtest/gtest.h>
#include "box.h"

using namespace std;

TEST(box, string_constructor_normal)
{
  map<string, capd::interval> edges;
  edges.insert(make_pair("a", capd::interval("0", "1")));
  edges.insert(make_pair("b", capd::interval("-0.1", "0.1")));
  edges.insert(make_pair("c_index", capd::interval("0", "0")));
  EXPECT_EQ(box(edges), box("a : [0,1];b:[ -0.1, 0.1];c_index:[0,  0];"));
  EXPECT_EQ(box(edges), box("b:[ -0.1, 0.1];c_index:[0,  0];a : [0,1];"));
}

TEST(box, string_constructor_excpetion)
{
  EXPECT_THROW(
    box("a : [0,1];b:[ -0.1, 0.1];c_index:[0,  0]"), invalid_argument);
}

TEST(compatible, compatible_boxes)
{
  box b("a:[0,1];b:[0,1];c:[0,1];");
  EXPECT_TRUE(b.compatible(box("a:[0,0.5];b:[0.5,0.5];c:[0.5,1];")));
  EXPECT_TRUE(box().compatible(box()));
}

TEST(compatible, boxes_are_not_compatible)
{
  box b("a:[0,1];b:[0,1];");
  EXPECT_FALSE(b.compatible(box("a:[0,0.5];b:[0.5,0.5];c:[0.5,1];")));
  EXPECT_FALSE(box().compatible(box("c:[0,1];")));
  EXPECT_FALSE(b.compatible(box()));
  EXPECT_TRUE(b.compatible(box("b:[-20, 54]; a:[0.12, 94.2];")));
}

TEST(empty, normal_test)
{
  box b("a:[0,1];b:[0,1];");
  EXPECT_FALSE(b.empty());
  box a;
  EXPECT_TRUE(a.empty());
  EXPECT_TRUE(box().empty());
}

TEST(get_vars, normal_test)
{
  box b("c:[-0.43,342];a:[0,1];b:[0,1];");
  EXPECT_TRUE(b.get_vars() == set<string>({"a", "c", "b"}));
  EXPECT_TRUE(b.get_vars() == set<string>({"b", "c", "a"}));
  EXPECT_FALSE(b.get_vars() == set<string>({"b", "c", "d"}));
}

TEST(get_vars, empty_boxes)
{
  EXPECT_TRUE(box().get_vars() == box().get_vars());
  box b("c:[-0.43,342];a:[0,1];b:[0,1];");
  EXPECT_FALSE(b.get_vars() == box().get_vars());
}

TEST(get_map, immutability)
{
  box b("c:[-0.43,342];a:[0,1];b:[0,1];");
  map<string, capd::interval> edges = b.get_map();
  map<string, capd::interval> tmp{
    {"a", capd::interval("0", "1")},
    {"b", capd::interval("0", "1")},
    {"c", capd::interval("-0.43", "342")}};
  EXPECT_TRUE(edges == tmp);
  map<string, capd::interval> tmp2{
    {"a", capd::interval(0, 1)},
    {"b", capd::interval(0, 1)},
    {"c", capd::interval(-0.43, 342)}};
  EXPECT_FALSE(edges == tmp2);
  edges["a"] = capd::interval("-1", "0");
  EXPECT_FALSE(edges == b.get_map());
}

TEST(contains, cases)
{
  box b("a:[0,1];b:[0,1];c:[0,1];");
  EXPECT_TRUE(b.contains(box("a:[0,0.5];b:[0.5,0.5];c:[0.5,1];")));
  EXPECT_FALSE(b.contains(box("a:[0.1,1.1];b:[0,1];c:[0,1];")));
  EXPECT_TRUE(b.contains(box("a:[0.0,1.0];b:[0,1];c:[0,1];")));
  EXPECT_TRUE(box().contains(box()));
}

TEST(intersects, cases)
{
  box b("a:[0,1];b:[0,1];c:[0,1];");
  EXPECT_TRUE(b.intersects(box("a:[0,1];b:[0,1];c:[0,1];")));
  EXPECT_TRUE(b.intersects(box("a:[1,2];b:[1,2];c:[1,2];")));
  EXPECT_TRUE(b.intersects(box("a:[0.78,0.78];b:[0.78,0.78];c:[0.78,0.78];")));
  EXPECT_FALSE(b.intersects(box("a:[1.0001,2];b:[1,2];c:[1,2];")));
  EXPECT_FALSE(b.intersects(box("a:[1.0001,1.9];b:[1,2];c:[1,2];")));
  EXPECT_TRUE(b.contains(box("a:[0,0.5];b:[0.5,0.5];c:[0.5,1];")));
  EXPECT_TRUE(box().intersects(box()));
}

TEST(mid, normal)
{
  map<string, capd::interval> b_map{
    {"a", capd::interval(0, 1)},
    {"b", capd::interval(-1, 1)},
    {"c", capd::interval(-4.1, 3.2)}};
  box b(b_map);
  map<string, capd::interval> mid_map{
    {"a", capd::interval(0.49999, 0.50001)},
    {"b", capd::interval(-0.00001, 0.00001)},
    {"c", capd::interval(-0.45001, -0.44999)}};
  box mid(mid_map);
  EXPECT_TRUE(mid.contains(b.mid()));
  EXPECT_EQ(box().mid(), box());
}
