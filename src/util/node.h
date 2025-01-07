//
// Created by fedor on 28/11/18.
//

#ifndef PROBREACH_NODE_H
#define PROBREACH_NODE_H

#include <iostream>
#include <map>
#include <vector>

namespace pdrh
{
// node of the tree of mathematical expression
class node
{
public:
  // either a name of operation or a value of the operand (const or identifier)
  std::string value;
  // vector is empty if the node is terminal and non-empty if the node is
  // operation node
  std::vector<node *> operands;

  // Create a "node" from a "string" value.
  node(std::string value) : value(value)
  {
  }

  // Create a "node" from a "double" value. A double is converted to its
  // string representation using the first 16 digit after the decimal point
  node(double v);

  node(const node &rhs) : value(rhs.value), operands(rhs.operands)
  {
  }

  node(const std::string value, const std::vector<node *> operands)
    : value(value), operands(operands)
  {
  }

  node()
  {
  }

  node &operator=(const node &rhs)
  {
    value = rhs.value;
    operands = rhs.operands;
    return *this;
  }

  // implement the correct comparison of two vectors
  bool operator==(const node &rhs)
  {
    return (value == rhs.value) && (operands == rhs.operands);
  }

  bool operator!=(const node &rhs)
  {
    return !(*this == rhs);
  }

  friend std::ostream &operator<<(std::ostream &os, const node &n);
};

node *copy_node(node *);
void copy_tree(node *&, node *);
void delete_node(node *);

double node_to_double(pdrh::node *);
double node_to_double(pdrh::node *, std::map<std::string, double>);
bool node_to_boolean(pdrh::node *, std::map<std::string, double>);
bool node_zero_crossing(
  pdrh::node *,
  std::map<std::string, double>,
  std::map<std::string, double>);

std::string node_to_string_prefix(node *);
std::string node_to_string_infix(node *);

std::string node_fix_index(node *, int, std::string);
bool is_node_empty(node *);

// we might not need these methods in future
void get_first_node_by_value(node *, node *, std::vector<std::string>);
pdrh::node *get_node_neg_by_value(pdrh::node *, std::vector<std::string>);
} // namespace pdrh

#endif // PROBREACH_NODE_H
