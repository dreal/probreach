//
// Created by fedor on 28/11/18.
//

#include "node.h"
#include "model.h"
#include <sstream>
#include <random>
#include <cmath>
#include <algorithm>
#include <iomanip>

using namespace std;
using namespace pdrh;


node::node(double v)
{
  std::stringstream ss;
  ss << std::setprecision(16);
  ss << v;
  this->value = ss.str();
}


std::ostream &pdrh::operator<<(std::ostream &os, const node &n)
{
  if (n.operands.size() > 1)
  {
    os << "(";
    for (int i = 0; i < n.operands.size() - 1; i++)
    {
      os << n.operands.at(i);
      os << n.value;
    }
    os << n.operands.at(n.operands.size() - 1) << ")";
  }
  else if (n.operands.size() == 1)
  {
    if (n.value == "-")
      os << "(" << n.value << n.operands.front() << ")";
    else
      os << n.value << "(" << n.operands.front() << ")";
  }
  else
    os << n.value;
  
  return os;
}

/**
 * Getting a string representation of the node in prefix notation.
 *
 * @param n - pointer to the root of the expression tree.
 * @return node in prefix notation as string.
 */
string pdrh::node_to_string_prefix(pdrh::node *n)
{
  stringstream s;
  // checking whether n is an operation node
  if (n->operands.size() > 0)
  {
    s << "(" << n->value;
    for (pdrh::node *op : n->operands)
    {
      s << pdrh::node_to_string_prefix(op);
    }
    s << ")";
  }
  else
  {
    s << " " << n->value;
  }
  return s.str();
}

/**
 * Getting a string representation of the node in infix notation.
 *
 * @param n - pointer to the root of the expression tree.
 * @return node in infix notation as string.
 */
string pdrh::node_to_string_infix(pdrh::node *n)
{
  stringstream s;
  s << *n;
  return s.str();
}

/**
 * Getting a string representation of the node in prefix notation with the fixed index.
 *
 * @param n - pointer to the root of the expression tree.
 * @param step - depth in the path.
 * @param index - an identifier.
 * @return node with fixed index as string.
 */
string pdrh::node_fix_index(pdrh::node *n, int step, string index)
{
  stringstream s;
  // checking whether n is an operation node
  if (n->operands.size() > 0)
  {
    s << "(" << n->value;
    for (pdrh::node *op : n->operands)
    {
      s << pdrh::node_fix_index(op, step, index);
    }
    s << ")";
  }
  else
  {
    //        if(pdrh::var_map.find(n->value) != pdrh::var_map.end())
    // only performing a soft check here whether the value is digit or an identifier
    if (isdigit(n->value.front()) || n->value == "true" || n->value == "false")
    {
      s << " " << n->value;
    }
    else
    {
      s << " " << n->value << "_" << step << "_" << index;
    }
  }
  return s.str();
}

/**
 * Computes the value of the node provided as the first arguments at the point specified by the second argument.
 *
 * @param n - root node of the expression tree.
 * @param vals - map defining the point.
 * @return value of the node.
 */
double pdrh::node_to_double(pdrh::node *n, std::map<std::string, double> vals)
{
  // terminal node
  if (n->operands.size() == 0)
  {
    // returning a value only if the variable from the node appears in the vector of values
    if (vals.find(n->value) != vals.end())
    {
      return vals[n->value];
    }
    // in case of infinity
    else if (n->value == "-infty")
    {
      return -numeric_limits<double>::max();
    }
    else if (n->value == "infty")
    {
      return numeric_limits<double>::max();
    }
    // in case of a constant
    double val;
    istringstream s(n->value);
    s >> val;
    return val;
  }
  // operation node
  else
  {
    if (n->value == "+")
    {
      // unary plus
      if (n->operands.size() == 1)
      {
        return node_to_double(n->operands.front(), vals);
      }
      // summation
      else if (n->operands.size() == 2)
      {
        return node_to_double(n->operands.front(), vals) +
               node_to_double(n->operands.back(), vals);
      }
    }
    else if (n->value == "-")
    {
      // unary minus
      if (n->operands.size() == 1)
      {
        return -node_to_double(n->operands.front(), vals);
      }
      // subtraction
      else if (n->operands.size() == 2)
      {
        return node_to_double(n->operands.front(), vals) -
               node_to_double(n->operands.back(), vals);
      }
    }
    else if (n->value == "*")
    {
      return node_to_double(n->operands.front(), vals) *
             node_to_double(n->operands.back(), vals);
    }
    else if (n->value == "/")
    {
      return node_to_double(n->operands.front(), vals) /
             node_to_double(n->operands.back(), vals);
    }
    else if (n->value == "^")
    {
      return std::pow(
        node_to_double(n->operands.front(), vals),
        node_to_double(n->operands.back(), vals));
    }
    else if (n->value == "sqrt")
    {
      return std::sqrt(node_to_double(n->operands.front(), vals));
    }
    else if (n->value == "abs")
    {
      return std::abs(node_to_double(n->operands.front(), vals));
    }
    else if (n->value == "exp")
    {
      return std::exp(node_to_double(n->operands.front(), vals));
    }
    else if (n->value == "log")
    {
      return std::log(node_to_double(n->operands.front(), vals));
    }
    else if (n->value == "sin")
    {
      return std::sin(node_to_double(n->operands.front(), vals));
    }
    else if (n->value == "cos")
    {
      return std::cos(node_to_double(n->operands.front(), vals));
    }
    else if (n->value == "tan")
    {
      return std::tan(node_to_double(n->operands.front(), vals));
    }
    else if (n->value == "asin")
    {
      return std::asin(node_to_double(n->operands.front(), vals));
    }
    else if (n->value == "acos")
    {
      return std::acos(node_to_double(n->operands.front(), vals));
    }
    else if (n->value == "atan")
    {
      return std::atan(node_to_double(n->operands.front(), vals));
    }
    if (n->value == "dist_normal")
    {
      std::random_device rd;
      std::mt19937 gen(rd());
      double mean = node_to_double(n->operands[0], vals);
      double stddev = node_to_double(n->operands[1], vals);

      std::normal_distribution<> dist(mean, stddev);
      return dist(gen);
    }
    else if (n->value == "dist_uniform")
    {
      std::random_device rd;
      std::mt19937 gen(rd());
      double left = node_to_double(n->operands[0], vals);
      double right = node_to_double(n->operands[1], vals);

      std::uniform_real_distribution<> dist(left, right);
      return dist(gen);
    }
    else if (n->value == "dist_gamma")
    {
      std::random_device rd;
      std::mt19937 gen(rd());
      double a = node_to_double(n->operands[0], vals);
      double b = node_to_double(n->operands[1], vals);

      std::gamma_distribution<> dist(a, b);
      return dist(gen);
    }
    else if (n->value == "dist_exp")
    {
      std::random_device rd;
      std::mt19937 gen(rd());
      double param = node_to_double(n->operands[0], vals);

      std::exponential_distribution<> dist(param);
      return dist(gen);
    }
    else if (n->value == "dist_discrete")
    {
      std::random_device rd;
      std::mt19937 gen(rd());
      vector<double> weights;
      for (node *op : n->operands)
      {
        weights.push_back(node_to_double(op->operands[1], vals));
      }

      std::discrete_distribution<int> dist(weights.begin(), weights.end());
      int i = dist(gen);
      return node_to_double(n->operands[i]->operands[0], vals);
    }
    else
    {
      cerr << "Unknown function \"" << n->value << "\"";
      exit(EXIT_FAILURE);
    }
  }
}

/**
 * Computes the value of the node.
 *
 * @param n - root node of the expression tree.
 * @return - value of the node.
 */
double pdrh::node_to_double(pdrh::node *n)
{
  return node_to_double(n, std::map<string, double>());
}

/**
 * Evaluates the value of a predicate at the point. Throws an exception in case
 * if one of the terminal modes is not a number.
 *
 * @param n - predicate to be evaluated.
 * @param vals - point for which the evaluation is performed
 * @return
 */
bool pdrh::node_to_boolean(pdrh::node *n, std::map<std::string, double> vals)
{
  // comparison operators
  if (n->value == ">=")
  {
    return node_to_double(n->operands.front(), vals) >=
           node_to_double(n->operands.back(), vals);
  }
  else if (n->value == ">")
  {
    return node_to_double(n->operands.front(), vals) >
           node_to_double(n->operands.back(), vals);
  }
  else if (n->value == "=")
  {
    return node_to_double(n->operands.front(), vals) ==
           node_to_double(n->operands.back(), vals);
  }
  else if (n->value == "<")
  {
    return node_to_double(n->operands.front(), vals) <
           node_to_double(n->operands.back(), vals);
  }
  else if (n->value == "<=")
  {
    return node_to_double(n->operands.front(), vals) <=
           node_to_double(n->operands.back(), vals);
  }
  else if (n->value == "and")
  {
    bool res = true;
    for (pdrh::node *nd : n->operands)
    {
      res = res && node_to_boolean(nd, vals);
    }
    return res;
  }
  else if (n->value == "or")
  {
    bool res = false;
    for (pdrh::node *nd : n->operands)
    {
      res = res || node_to_boolean(nd, vals);
    }
    return res;
  }
  else
  {
    cerr << "Unrecognised or unsupported operation \"" << n->value << "\"";
    exit(EXIT_FAILURE);
  }
}

/**
 * Copies the entire tree given its root
 *
 * @param copy - root node for the copy of the tree
 * @param origin - root node for the original tree
 */
void pdrh::copy_tree(pdrh::node *&copy, pdrh::node *origin)
{
  copy->value = origin->value;
  for (pdrh::node *child : origin->operands)
  {
    pdrh::node *copy_operand = new pdrh::node;
    pdrh::copy_tree(copy_operand, child);
    copy->operands.push_back(copy_operand);
  }
}

/**
 * Creates a copy of the node.
 *
 * @param origin - original node
 * @return the copy of the node
 */
pdrh::node *pdrh::copy_node(node *origin)
{
  pdrh::node *copy = new pdrh::node();
  copy_tree(copy, origin);
  return copy;
}

/**
 * Creating a string representation of the node in prefix notation
 * @param n - node to delete
 */
void pdrh::delete_node(pdrh::node *n)
{
  for (pdrh::node *op : n->operands)
  {
    delete_node(op);
  }
  delete n;
}

/**
 * Checking if the node is empty.
 *
 * @param n - node to check.
 * @return emptiness check result.
 */
bool pdrh::is_node_empty(node *n)
{
  return n->value.empty() && n->operands.empty();
}

/**
 * Returns true if zero-crossing happens between the left-handside and the right-handside points.
 *
 *
 * @param expr - expression to check.
 * @param left - left point.
 * @param right - right point.
 * @return the result of zero-crossing check
 */
bool pdrh::node_zero_crossing(
  pdrh::node *expr,
  std::map<std::string, double> left,
  std::map<std::string, double> right)
{
  // comparison operators
  if (
    expr->value == ">=" || expr->value == ">" || expr->value == "=" ||
    expr->value == "<" || expr->value == "<=")
  {
    return (node_to_double(expr->operands.front(), left) -
            node_to_double(expr->operands.back(), left)) *
             (node_to_double(expr->operands.front(), right) -
              node_to_double(expr->operands.back(), right)) <
           0;
  }
  else if (expr->value == "and")
  {
    bool res = true;
    for (pdrh::node *n : expr->operands)
    {
      res = res && node_zero_crossing(n, left, right);
    }
    return res;
  }
  else if (expr->value == "or")
  {
    bool res = true;
    for (pdrh::node *n : expr->operands)
    {
      res = res || node_zero_crossing(n, left, right);
    }
    return res;
  }
  else
  {
    cerr << "Unrecognised or unsupported operation \"" << expr->value << "\"";
    exit(EXIT_FAILURE);
  }
}

/**
 * Returns the first node matching the pattern (root->value == values[i]) and (expr).
 *
 * @param root - root of the tree.
 * @param res_node - resulting node.
 * @param values - list of values to check.
 */
void pdrh::get_first_node_by_value(
  node *root,
  node *res_node,
  vector<string> values)
{
  if (root->value == "=")
  {
    for (pdrh::node *child : root->operands)
    {
      if (find(values.begin(), values.end(), child->value) != values.end())
      {
        *res_node = *root;
        root->value = "true";
        root->operands.clear();
      }
      else
      {
        pdrh::get_first_node_by_value(child, res_node, values);
      }
    }
  }
  else
  {
    for (pdrh::node *child : root->operands)
    {
      pdrh::get_first_node_by_value(child, res_node, values);
    }
  }
}

/**
 * Returns the first node matching the pattern (root->value == values[i]) and (!expr)
 *
 * @param root - root of the tree.
 * @param values - resulting node.
 * @return
 */
node *pdrh::get_node_neg_by_value(node *root, vector<string> values)
{
  pdrh::node *root_copy = new pdrh::node();
  pdrh::copy_tree(root_copy, root);
  pdrh::node *time_node = new pdrh::node;
  pdrh::get_first_node_by_value(root_copy, time_node, values);
  //cout << "Node before removing time node: " << pdrh::node_to_string_prefix(root) << endl;
  if (pdrh::is_node_empty(time_node))
    return NULL;
  // creating a negation node
  pdrh::node *not_node = new node("not", {root_copy});
  // creating a resulting node
  pdrh::node *res_node = new node("and", {time_node, not_node});
  //cout << "RES TIME NODE: " << pdrh::node_to_string_prefix(res_node) << endl;
  return res_node;
}
