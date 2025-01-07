//
// Created by fedor on 26/12/15.
//
#include <capd/capdlib.h>
#include <capd/intervals/lib.h>

#include <algorithm>
#include <cmath>

#include "box.h"

using namespace std;

/// Creates a box that does not contain any intervals.
box::box()
{
}

/// Creates a box from a map, where keys represent variables names,
/// and values contain their corresponding intervals.
box::box(std::map<std::string, capd::interval> e)
{
  for (auto it = e.cbegin(); it != e.cend(); it++)
  {
    if (capd::intervals::width(it->second) < 0)
    {
      std::ostringstream s;
      s << "invalid interval " << it->first << ":" << it->second
        << " while creating a box";
      throw std::invalid_argument(s.str());
    }
  }
  edges = e;
}

box::box(vector<box> boxes)
{
  for (box b : boxes)
  {
    std::map<string, capd::interval> b_map = b.get_map();
    for (auto it = b_map.begin(); it != b_map.end(); it++)
    {
      edges.insert(make_pair(it->first, it->second));
    }
  }
}

/// Constructs a box from its string representation (e.g., "a[0,1];b[-3,4];").
box::box(string line)
{
  // removing whitespaces
  line.erase(remove_if(line.begin(), line.end(), ::isspace), line.end());
  size_t pos = 0;
  map<string, capd::interval> b_map;
  while (line.length() > 0)
  {
    pos = line.find(";");
    if (pos == string::npos)
    {
      ostringstream s;
      s << "Every variable definition must finish with \";\"";
      throw invalid_argument(s.str());
    }

    string edge_string = line.substr(0, pos);
    line.erase(0, pos + 1);

    size_t pos2 = edge_string.find(":");
    string var = edge_string.substr(0, pos2);

    string interval_string =
      edge_string.substr(pos2 + 1, edge_string.length() - pos2);

    size_t pos3 = interval_string.find(",");
    b_map.insert(make_pair(
      var,
      capd::interval(
        interval_string.substr(1, pos3 - 1),
        interval_string.substr(
          pos3 + 1, interval_string.length() - pos3 - 2))));
  }
  edges = b_map;
}

/// Returns true if the box does not have any edges
bool box::empty() const
{
  return edges.empty();
}

/// Removes specified variable (together with its interval) from the box
void box::erase(string var)
{
  edges.erase(var);
}

/// Returns a map representation of the box, whether the map keys contain
/// the edges names, and the map values contain the intervals
/// representing the edges
std::map<std::string, capd::interval> box::get_map() const
{
  return edges;
}

/// Returns the list of invervals comprising the box edges
std::vector<capd::interval> box::get_intervals() const
{
  std::vector<capd::interval> i;
  for (auto it = edges.cbegin(); it != edges.cend(); it++)
  {
    i.push_back(it->second);
  }
  return i;
}

/// Returns the box variables
std::set<std::string> box::get_vars() const
{
  std::set<std::string> vars;
  for (auto it = edges.cbegin(); it != edges.cend(); it++)
  {
    vars.insert(it->first);
  }
  return vars;
}

bool box::contains(box b) const
{
  map<string, capd::interval> edges = get_map();
  map<string, capd::interval> b_edges = b.get_map();
  for (auto it = b_edges.cbegin(); it != b_edges.cend(); it++)
  {
    if (edges.find(it->first) != edges.cend())
    {
      if (!edges[it->first].contains(it->second))
      {
        return false;
      }
    }
    else
    {
      ostringstream s;
      s << "The target box does not contain variable: \"" << it->first << "\"";
      throw invalid_argument(s.str());
    }
  }
  return true;
}

bool box::intersects(box b) const
{
  for (auto it = edges.cbegin(); it != edges.cend(); it++)
  {
    if (b.get_map().find(it->first) != b.get_map().cend())
    {
      if (!(it->second.contains(b.get_map()[it->first].leftBound()) ||
            it->second.contains(b.get_map()[it->first].rightBound()) ||
            b.get_map()[it->first].contains(it->second.leftBound()) ||
            b.get_map()[it->first].contains(it->second.rightBound())))
      {
        return false;
      }
    }
    else
    {
      ostringstream s;
      s << "The target box does not contain variable: \"" << it->first << "\"";
      throw invalid_argument(s.str());
    }
  }
  return true;
}

bool box::compatible(box b) const
{
  return (get_vars() == b.get_vars());
}

std::ostream &operator<<(std::ostream &os, const box &b)
{
  std::map<std::string, capd::interval> e = b.get_map();
  for (auto it = e.cbegin(); it != e.cend(); it++)
    os << it->first << ":" << it->second << "; ";

  return os;
}

bool operator<(const box &lhs, const box &rhs)
{
  // checking if dimensions of the boxes are the same
  if (lhs.get_vars() != rhs.get_vars())
  {
    std::stringstream s;
    s << "Variables of the compared boxes are not the same";
    throw std::invalid_argument(s.str());
  }
  std::map<std::string, capd::interval> lhs_map = lhs.get_map();
  std::map<std::string, capd::interval> rhs_map = rhs.get_map();
  for (auto it = lhs_map.cbegin(); it != lhs_map.cend(); it++)
  {
    if (it->second.leftBound() < rhs_map[it->first].leftBound())
    {
      return true;
    }
    if (it->second.leftBound() > rhs_map[it->first].leftBound())
    {
      return false;
    }
  }
  return false;
}

bool operator==(const box &lhs, const box &rhs)
{
  // checking if dimensions of the boxes are the same
  if (lhs.get_vars() != rhs.get_vars())
  {
    std::stringstream s;
    s << "Variables of the compared boxes are not the same";
    throw std::invalid_argument(s.str());
  }
  std::map<std::string, capd::interval> lhs_map = lhs.get_map();
  std::map<std::string, capd::interval> rhs_map = rhs.get_map();
  for (auto it = lhs_map.cbegin(); it != lhs_map.cend(); it++)
  {
    if (
      (it->second.leftBound() != rhs_map[it->first].leftBound()) ||
      (it->second.rightBound() != rhs_map[it->first].rightBound()))
    {
      return false;
    }
  }
  return true;
}

box operator+(const box &lhs, const box &rhs)
{
  if (!lhs.get_keys_diff(rhs).empty() || !rhs.get_keys_diff(lhs).empty())
  {
    ostringstream s;
    s << "cannot perform \"+\" operation for " << lhs << " and " << rhs
      << ". The boxes have different sets of variables";
    throw std::invalid_argument(s.str());
  }
  map<string, capd::interval> lhs_map = lhs.get_map();
  map<string, capd::interval> rhs_map = rhs.get_map();
  map<string, capd::interval> res;
  for (auto it = lhs_map.cbegin(); it != lhs_map.cend(); it++)
  {
    res.insert(make_pair(it->first, it->second + rhs_map[it->first]));
  }
  return box(res);
}

box operator-(const box &lhs, const box &rhs)
{
  if (!lhs.get_keys_diff(rhs).empty() || !rhs.get_keys_diff(lhs).empty())
  {
    ostringstream s;
    s << "cannot perform \"+\" operation for " << lhs << " and " << rhs
      << ". The boxes have different sets of variables";
    throw std::invalid_argument(s.str());
  }
  map<string, capd::interval> lhs_map = lhs.get_map();
  map<string, capd::interval> rhs_map = rhs.get_map();
  map<string, capd::interval> res;
  for (auto it = lhs_map.cbegin(); it != lhs_map.cend(); it++)
  {
    res.insert(make_pair(it->first, it->second - rhs_map[it->first]));
  }
  return box(res);
}

box operator*(const box &lhs, const box &rhs)
{
  if (!lhs.get_keys_diff(rhs).empty() || !rhs.get_keys_diff(lhs).empty())
  {
    ostringstream s;
    s << "cannot perform \"+\" operation for " << lhs << " and " << rhs
      << ". The boxes have different sets of variables";
    throw std::invalid_argument(s.str());
  }
  map<string, capd::interval> lhs_map = lhs.get_map();
  map<string, capd::interval> rhs_map = rhs.get_map();
  map<string, capd::interval> res;
  for (auto it = lhs_map.cbegin(); it != lhs_map.cend(); it++)
  {
    res.insert(make_pair(it->first, it->second * rhs_map[it->first]));
  }
  return box(res);
}

box operator/(const box &lhs, const box &rhs)
{
  if (!lhs.get_keys_diff(rhs).empty() || !rhs.get_keys_diff(lhs).empty())
  {
    ostringstream s;
    s << "cannot perform \"+\" operation for " << lhs << " and " << rhs
      << ". The boxes have different sets of variables";
    throw std::invalid_argument(s.str());
  }
  map<string, capd::interval> lhs_map = lhs.get_map();
  map<string, capd::interval> rhs_map = rhs.get_map();
  map<string, capd::interval> res;
  for (auto it = lhs_map.cbegin(); it != lhs_map.cend(); it++)
  {
    res.insert(make_pair(it->first, it->second / rhs_map[it->first]));
  }
  return box(res);
}

box operator/(const box &lhs, double rhs)
{
  if (rhs == 0)
  {
    ostringstream s;
    s << "cannot devide by 0";
    throw std::invalid_argument(s.str());
  }
  map<string, capd::interval> lhs_map = lhs.get_map();
  map<string, capd::interval> res;
  for (auto it = lhs_map.cbegin(); it != lhs_map.cend(); it++)
  {
    res.insert(make_pair(it->first, it->second / rhs));
  }
  return box(res);
}

box box::get_mean()
{
  map<string, capd::interval> edges = get_map();
  map<string, capd::interval> mu_map;
  for (auto it = edges.cbegin(); it != edges.cend(); it++)
  {
    mu_map.insert(make_pair(it->first, it->second.mid()));
  }
  return box(mu_map);
}

box box::get_stddev()
{
  map<string, capd::interval> edges = get_map();
  map<string, capd::interval> sigma_map;
  for (auto it = edges.cbegin(); it != edges.cend(); it++)
  {
    sigma_map.insert(make_pair(
      it->first,
      capd::intervals::width(
        capd::interval(it->second.leftBound(), it->second.mid().leftBound()))));
  }
  return box(sigma_map);
}

double box::max_coordinate_value()
{
  double max = edges.cbegin()->second.leftBound();
  for (auto it = edges.cbegin(); it != edges.cend(); it++)
  {
    if (it->second.leftBound() > max)
    {
      max = it->second.leftBound();
    }
  }
  return max;
}

double box::max_side_width()
{
  double max = capd::intervals::width(edges.cbegin()->second);
  for (auto it = edges.cbegin(); it != edges.cend(); it++)
  {
    if (capd::intervals::width(it->second) > max)
    {
      max = capd::intervals::width(it->second);
    }
  }
  return max;
}

double box::min_side_width()
{
  double min = capd::intervals::width(edges.cbegin()->second);
  for (auto it = edges.cbegin(); it != edges.cend(); it++)
  {
    if (capd::intervals::width(it->second) < min)
    {
      min = capd::intervals::width(it->second);
    }
  }
  return min;
}

box box::get_keys_diff(box b) const
{
  map<string, capd::interval> res;
  map<string, capd::interval> lhs_map = get_map();
  map<string, capd::interval> rhs_map = b.get_map();
  for (auto it = lhs_map.cbegin(); it != lhs_map.cend(); it++)
  {
    if (rhs_map.find(it->first) == rhs_map.cend())
    {
      res.insert(make_pair(it->first, it->second));
    }
  }
  return box(res);
}

box box::fmod(int mod)
{
  map<string, capd::interval> res;
  for (auto it = this->edges.begin(); it != this->edges.end(); it++)
  {
    res.insert(make_pair(
      it->first,
      this->edges[it->first].leftBound() -
        (long)this->edges[it->first].leftBound()));
  }
  return box(res);
}

box box::sqrt()
{
  map<string, capd::interval> res;
  for (auto it = edges.cbegin(); it != edges.cend(); it++)
  {
    res.insert(make_pair(it->first, capd::intervals::sqrt(it->second)));
  }
  return box(res);
}

box box::log()
{
  map<string, capd::interval> res;
  for (auto it = edges.cbegin(); it != edges.cend(); it++)
  {
    res.insert(make_pair(it->first, capd::intervals::log(it->second)));
  }
  return box(res);
}
