//
// Created by fedor on 02/02/17.
//

#include "node.h"

#include <gtest/gtest.h>

using namespace std;

TEST(string_to_infix, normal) {
  EXPECT_STREQ(string("a").c_str(), node("a").to_infix().c_str());
  EXPECT_STREQ(
      string("(a+b)").c_str(),
      node("+", vector<node>{node("a"), node("b")}).to_infix().c_str());
}

TEST(string_to_prefix, normal) {
  EXPECT_STREQ(string(" a").c_str(), node("a").to_prefix().c_str());
  EXPECT_STREQ(
      string("(+ a b)").c_str(),
      node("+", vector<node>{node("a"), node("b")}).to_prefix().c_str());
}

TEST(append, normal) {
  node plus("+", vector<node>{node("a"), node("b"), node("c")});
  node minus("-", vector<node>{node("d"), node("e"), node("f")});
  node mult("*");
  mult.append(vector<node>{plus, minus});
  EXPECT_STREQ(string("((a+b+c)*(d-e-f))").c_str(), mult.to_infix().c_str());
}