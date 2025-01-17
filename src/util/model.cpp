//
// Created by fedor on 24/01/16.
//

#include "model.h"
#include "pdrh2box.h"
#include <string.h>
#include <iomanip>
#include <cmath>
#include <sstream>
#include <algorithm>
#include <capd/capdlib.h>
#include <capd/intervals/lib.h>

using namespace std;

pdrh::type pdrh::model_type;
pair<pdrh::node *, pdrh::node *> pdrh::time;
map<string, tuple<pdrh::node *, pdrh::node *, pdrh::node *, pdrh::node *>>
  pdrh::rv_map;
map<string, string> pdrh::rv_type_map;
map<string, map<pdrh::node *, pdrh::node *>> pdrh::dd_map;
map<string, pair<pdrh::node *, pdrh::node *>> pdrh::var_map;
map<string, string> pdrh::const_map;
map<string, pair<pdrh::node *, pdrh::node *>> pdrh::par_map;
map<string, pdrh::node *> pdrh::syn_map;
vector<pdrh::mode> pdrh::modes;
vector<pdrh::state> pdrh::init;
vector<pdrh::state> pdrh::goal;
vector<vector<pdrh::mode *>> pdrh::paths;

map<string, pair<pdrh::node *, pdrh::node *>> pdrh::distribution::uniform;
map<string, pair<pdrh::node *, pdrh::node *>> pdrh::distribution::normal;
map<string, pdrh::node *> pdrh::distribution::exp;
map<string, pair<pdrh::node *, pdrh::node *>> pdrh::distribution::gamma;

// adding a variable
void pdrh::push_var(string var, pdrh::node *left, pdrh::node *right)
{
  // COMMENTED OUT UNTIL ALL DEPENDENCIES HAS BEEN RESOLVED
  // setting initial domain to (-infty, infty)
  //    capd::interval domain(-numeric_limits<double>::infinity(), numeric_limits<double>::infinity());
  //    if(strcmp(left->value.c_str(), "-infty") != 0)
  //    {
  //        domain.setLeftBound(pdrh::node_to_interval(left).leftBound());
  //    }
  //    if(strcmp(right->value.c_str(), "infty") != 0)
  //    {
  //        domain.setRightBound(pdrh::node_to_interval(right).rightBound());
  //    }
  //    // checking the width of the domain
  //    if(capd::intervals::width(domain) < 0)
  //    {
  //        stringstream s;
  //        s << "invalid domain " << domain << " for variable \"" << var << "\"";
  //        throw invalid_argument(s.str());
  //    }
  if (pdrh::var_map.find(var) != pdrh::var_map.cend())
  {
    stringstream s;
    s << "multiple declaration of \"" << var << "\"";
    throw invalid_argument(s.str());
  }
  else
  {
    pdrh::var_map.insert(make_pair(var, make_pair(left, right)));
  }
}

// adding time bounds
void pdrh::push_time_bounds(pdrh::node *left, pdrh::node *right)
{
  // COMMENTED OUT UNTIL ALL DEPENDENCIES HAS BEEN RESOLVED
  //    capd::interval domain(pdrh::node_to_interval(left).leftBound(), pdrh::node_to_interval(right).rightBound());
  //    if(capd::intervals::width(domain) < 0)
  //    {
  //        stringstream s;
  //        s << "invalid time domain " << domain;
  //        throw invalid_argument(s.str());
  //    }
  pdrh::time = make_pair(left, right);
}

// adding invariant
void pdrh::push_invt(pdrh::mode &m, pdrh::node *invt)
{
  m.invts.push_back(invt);
}

// adding mode
void pdrh::push_mode(pdrh::mode m)
{
  vector<string> extra_vars = pdrh::get_keys_diff(pdrh::var_map, m.flow_map);
  for (string var : extra_vars)
  {
    m.flow_map.insert(make_pair(var, pdrh::var_map[var]));
    m.odes.insert(make_pair(var, new node("0")));
    if (pdrh::var_map[var].first != pdrh::var_map[var].second)
    {
      // adding this variable to the list of parameters if it is not there yet,
      // if it is not a continuous or discrete random variable and
      // if its domain is an interval of length descending than 0.
      // There might be a problem as the length of the interval
      // is always different from 0 due to overapproximation of
      // the interval arithmetics
      if (
        pdrh::par_map.find(var) == pdrh::par_map.cend() &&
        pdrh::rv_map.find(var) == pdrh::rv_map.cend() &&
        pdrh::dd_map.find(var) == pdrh::dd_map.cend() &&
        pdrh::var_map[var].first != pdrh::var_map[var].second)
      // COMMENTED OUT DUE TO DEPENDANCE ON INTERVAL ARITHMETIC
      //               capd::intervals::width(capd::interval(
      //                       node_to_interval(pdrh::var_map[var].first).leftBound(),
      //                       node_to_interval(pdrh::var_map[var].second).rightBound())) > 0)
      {
        bool insert_flag = true;
        for (pdrh::mode md : pdrh::modes)
        {
          if (md.flow_map.find(var) != md.flow_map.cend())
          {
            insert_flag = false;
            break;
          }
        }
        if (insert_flag)
        {
          pdrh::par_map.insert(make_pair(var, pdrh::var_map[var]));
        }
      }
    }
  }
  pdrh::modes.push_back(m);
}

// adding ode to the mode
void pdrh::push_ode(pdrh::mode &m, string var, pdrh::node *ode)
{
  if (pdrh::var_map.find(var) != pdrh::var_map.cend())
  {
    if (m.flow_map.find(var) == m.flow_map.cend())
    {
      m.flow_map.insert(make_pair(var, pdrh::var_map[var]));
      m.odes.insert(make_pair(var, ode));
      // removing a variable from the parameter list if there is an ode defined for it
      if (pdrh::par_map.find(var) != pdrh::par_map.cend())
      {
        pdrh::par_map.erase(var);
      }
    }
    else
    {
      stringstream s;
      s << "ode for the variable \"" << var << "\" was already declared above";
      throw invalid_argument(s.str());
    }
  }
  else
  {
    stringstream s;
    s << "variable \"" << var
      << "\" appears in the flow but it was not declared";
    throw invalid_argument(s.str());
  }
}

// adding a reset
void pdrh::push_reset(
  pdrh::mode &m,
  pdrh::mode::jump &j,
  string var,
  pdrh::node *expr)
{
  // implement error check
  j.reset.insert(make_pair(var, expr));
}

// adding a jump
void pdrh::push_jump(pdrh::mode &m, mode::jump j)
{
  m.jumps.push_back(j);
}

// adding init
void pdrh::push_init(vector<pdrh::state> s)
{
  pdrh::init = s;
}

// adding goal
void pdrh::push_goal(vector<pdrh::state> s)
{
  pdrh::goal = s;
}

void pdrh::push_path(vector<mode *> path)
{
  pdrh::paths.push_back(path);
}

// adding a parameter to synthesize
void pdrh::push_syn_pair(string var, pdrh::node *precision)
{
  pdrh::syn_map.insert(make_pair(var, precision));
}

// adding continuous random variable
void pdrh::push_rv(
  string var,
  pdrh::node *pdf,
  pdrh::node *left,
  pdrh::node *right,
  pdrh::node *start)
{
  pdrh::rv_map.insert(make_pair(var, make_tuple(pdf, left, right, start)));
}

// adding continuous random variable with its type
void pdrh::push_rv_type(string var, string type)
{
  pdrh::rv_type_map.insert(make_pair(var, type));
}

// adding discrete random variable
void pdrh::push_dd(string var, map<node *, node *> m)
{
  pdrh::dd_map.insert(make_pair(var, m));
}

// checking if the variable exists
bool pdrh::var_exists(string var)
{
  return (pdrh::var_map.find(var) != pdrh::var_map.cend());
}

// getting pointer to the mode by id
pdrh::mode *pdrh::get_mode(int id)
{
  for (size_t i = 0; i < pdrh::modes.size(); i++)
  {
    if (pdrh::modes.at(i).id == id)
    {
      return &pdrh::modes.at(i);
    }
  }
  return NULL;
}

pdrh::mode::jump pdrh::mode::get_jump(int id)
{
  for (size_t i = 0; i < this->jumps.size(); i++)
  {
    if (this->jumps.at(i).next_id == id)
    {
      return this->jumps.at(i);
    }
  }
}

// getting the shortest path between two modes
vector<pdrh::mode *> pdrh::get_shortest_path(pdrh::mode *begin, pdrh::mode *end)
{
  // initializing the set of paths
  vector<std::vector<pdrh::mode *>> paths;
  vector<pdrh::mode *> path;
  // checking if the initial state is the end state
  if (begin == end)
  {
    // pushing the initial mode to the initial path
    path.push_back(begin);
    return path;
  }
  else
  {
    // pushing the initial mode to the initial path
    path.push_back(begin);
    // pushing the initial path to the set of paths
    paths.push_back(path);
    while (!paths.empty())
    {
      // getting the first path in the set of paths
      path = paths.front();
      paths.erase(paths.cbegin());
      // getting the mode in the path
      pdrh::mode *cur_mode = path.back();
      vector<pdrh::mode *> successors = pdrh::get_successors(cur_mode);
      // proceeding if the current mode has successors
      if (!successors.empty())
      {
        // checking if one of the successors is the end mode
        if (
          std::find(successors.begin(), successors.end(), end) !=
          successors.cend())
        {
          path.push_back(end);
          paths.clear();
          return path;
        }
        else
        {
          // iterating through the successors of the current mode
          for (pdrh::mode *suc_mode : successors)
          {
            // checking if a successor does not appear in the current path
            if (find(path.begin(), path.end(), suc_mode) == path.cend())
            {
              vector<pdrh::mode *> tmp_path = path;
              tmp_path.push_back(suc_mode);
              paths.push_back(tmp_path);
            }
          }
        }
      }
    }
  }
  path.clear();
  return path;
}

// getting all paths of length path_length between begin and end modes
vector<vector<pdrh::mode *>>
pdrh::get_paths(pdrh::mode *begin, pdrh::mode *end, int path_length)
{
  // initializing the set of paths
  vector<std::vector<pdrh::mode *>> paths;
  vector<pdrh::mode *> path;
  path.push_back(begin);
  // initializing the stack
  vector<vector<pdrh::mode *>> stack;
  stack.push_back(path);
  while (!stack.empty())
  {
    // getting the first paths from the set of paths
    path = stack.front();
    stack.erase(stack.cbegin());
    // checking if the correct path of the required length is found
    if ((path.back() == end) && (path.size() == path_length + 1))
    {
      paths.push_back(path);
    }
    // proceeding only if the length of the current path is ascending then the required length
    else if (path.size() < path_length + 1)
    {
      // getting the last mode in the path
      pdrh::mode *cur_mode = path.back();
      // getting the successors of the mode
      vector<pdrh::mode *> successors = pdrh::get_successors(cur_mode);
      for (pdrh::mode *suc_mode : successors)
      {
        // appending the successor the current paths
        vector<pdrh::mode *> new_path = path;
        new_path.push_back(suc_mode);
        // pushing the new path to the set of the paths
        stack.push_back(new_path);
      }
    }
  }
  return paths;
}

// getting all paths specified by the key word "paths:"
vector<vector<pdrh::mode *>> pdrh::get_paths()
{
  if (pdrh::paths.size() > 0)
  {
    return pdrh::paths;
  }
  //    else
  //    {
  //        return get_all_paths();
  //    }
}

// comparing two paths alphabetically
bool compare_paths_ascending(vector<pdrh::mode *> lhs, vector<pdrh::mode *> rhs)
{
  if (lhs.size() < rhs.size())
  {
    return true;
  }
  else if (lhs.size() > rhs.size())
  {
    return false;
  }
  else
  {
    stringstream s;
    for (pdrh::mode *m : lhs)
    {
      s << m->id;
    }
    string lstring = s.str();
    s.str("");
    for (pdrh::mode *m : rhs)
    {
      s << m->id;
    }
    if (lstring.compare(s.str()) <= 0)
    {
      return true;
    }
    return false;
  }
}

// getting all paths of length path_length for all combinations of init and goal modes
vector<vector<pdrh::mode *>> pdrh::get_all_paths(int path_length)
{
  vector<vector<pdrh::mode *>> res;
  for (pdrh::state i : pdrh::init)
  {
    for (pdrh::state g : pdrh::goal)
    {
      vector<vector<pdrh::mode *>> paths = pdrh::get_paths(
        pdrh::get_mode(i.id), pdrh::get_mode(g.id), path_length);
      res.insert(res.end(), paths.begin(), paths.end());
    }
  }
  // sorting all paths if the ascending order
  sort(res.begin(), res.end(), compare_paths_ascending);
  return res;
}

vector<vector<pdrh::mode *>> pdrh::get_all_paths(int min_depth, int max_depth)
{
  vector<vector<pdrh::mode *>> res;
  for (int i = min_depth; i <= max_depth; i++)
  {
    vector<vector<pdrh::mode *>> paths = pdrh::get_all_paths(i);
    res.insert(res.end(), paths.begin(), paths.end());
  }
  // sorting all paths if the ascending order
  sort(res.begin(), res.end(), compare_paths_ascending);
  return res;
}

// getting successors of the mode m
vector<pdrh::mode *> pdrh::get_successors(pdrh::mode *m)
{
  vector<pdrh::mode *> res;
  for (pdrh::mode::jump j : m->jumps)
  {
    pdrh::mode *tmp = pdrh::get_mode(j.next_id);
    if (tmp != NULL)
    {
      res.push_back(tmp);
    }
    else
    {
      stringstream s;
      s << "mode \"" << j.next_id
        << "\" is not defined but appears in the jump: " << pdrh::print_jump(j);
      throw invalid_argument(s.str());
    }
  }
  return res;
}

// getting initial modes
vector<pdrh::mode *> pdrh::get_init_modes()
{
  vector<pdrh::mode *> res;
  for (pdrh::state st : pdrh::init)
  {
    pdrh::mode *tmp = pdrh::get_mode(st.id);
    if (tmp != NULL)
    {
      res.push_back(tmp);
    }
    else
    {
      stringstream s;
      s << "mode \"" << st.id << "\" is not defined but appears in the init";
      throw invalid_argument(s.str());
    }
  }
  return res;
}

// getting goal modes
vector<pdrh::mode *> pdrh::get_goal_modes()
{
  vector<pdrh::mode *> res;
  for (pdrh::state st : pdrh::goal)
  {
    pdrh::mode *tmp = pdrh::get_mode(st.id);
    if (tmp != NULL)
    {
      res.push_back(tmp);
    }
    else
    {
      stringstream s;
      s << "mode \"" << st.id << "\" is not defined but appears in the goal";
      throw invalid_argument(s.str());
    }
  }
  return res;
}

// getting a difference of the key sets of two maps
vector<string> pdrh::get_keys_diff(
  map<string, pair<pdrh::node *, pdrh::node *>> left,
  map<string, pair<pdrh::node *, pdrh::node *>> right)
{
  vector<string> res;
  for (auto it = left.cbegin(); it != left.cend(); it++)
  {
    if (right.find(it->first) == right.cend())
    {
      res.push_back(it->first);
    }
  }
  return res;
}

// getting string representation of the model
string pdrh::model_to_string()
{
  stringstream out;
  out << "MODEL TYPE: " << pdrh::model_type << endl;
  out << "VARIABLES:" << endl;
  for (auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
  {
    out << "|   " << it->first << " ["
        << pdrh::node_to_string_prefix(it->second.first) << ", "
        << pdrh::node_to_string_prefix(it->second.second) << "]" << endl;
  }
  out << "PARAMETERS:" << endl;
  for (auto it = pdrh::par_map.cbegin(); it != pdrh::par_map.cend(); it++)
  {
    out << "|   " << it->first << " ["
        << pdrh::node_to_string_prefix(it->second.first) << ", "
        << pdrh::node_to_string_prefix(it->second.second) << "]" << endl;
  }
  out << "CONTINUOUS RANDOM VARIABLES:" << endl;
  for (auto it = pdrh::rv_map.cbegin(); it != pdrh::rv_map.cend(); it++)
  {
    out << "|   pdf(" << it->first
        << ") = " << pdrh::node_to_string_infix(get<0>(it->second)) << "  | "
        << pdrh::node_to_string_prefix(get<1>(it->second)) << " |   "
        << pdrh::node_to_string_prefix(get<2>(it->second)) << "    |   "
        << pdrh::node_to_string_prefix(get<3>(it->second)) << endl;
  }
  out << "DISCRETE RANDOM VARIABLES:" << endl;
  for (auto it = pdrh::dd_map.cbegin(); it != pdrh::dd_map.cend(); it++)
  {
    out << "|   dd(" << it->first << ") = (";
    for (auto it2 = it->second.cbegin(); it2 != it->second.cend(); it2++)
    {
      cout << pdrh::node_to_string_prefix(it2->first) << " : "
           << pdrh::node_to_string_prefix(it2->second) << endl;
      out << pdrh::node_to_string_prefix(it2->first) << " : "
          << pdrh::node_to_string_prefix(it2->second) << ", ";
    }
    out << ")" << endl;
  }
  //    if(!pdrh::is_node_empty(pdrh::time.first) && !pdrh::is_node_empty(pdrh::time.second))
  //    {
  //        out << "TIME DOMAIN:" << endl;
  //        out << "|   [" << pdrh::node_to_string_prefix(pdrh::time.first) << ", " << pdrh::node_to_string_prefix(pdrh::time.second) << "]" << endl;
  //    }
  out << "MODES:" << endl;
  for (pdrh::mode m : pdrh::modes)
  {
    out << "|   MODE: " << m.id << ";" << endl;
    out << "|   TIME DOMAIN: [" << pdrh::node_to_string_prefix(m.time.first)
        << ", " << pdrh::node_to_string_prefix(m.time.second) << "]" << endl;
    out << "|   INVARIANTS:" << endl;
    for (pdrh::node *n : m.invts)
    {
      out << "|   |   " << pdrh::node_to_string_prefix(n) << endl;
    }
    out << "|   FLOW_MAP:" << endl;
    for (auto it = m.flow_map.cbegin(); it != m.flow_map.cend(); it++)
    {
      out << "|   " << it->first << " "
          << " [" << pdrh::node_to_string_prefix(it->second.first) << ", "
          << pdrh::node_to_string_prefix(it->second.second) << "]" << endl;
    }
    out << "|   ODES:" << endl;
    for (auto it = m.odes.cbegin(); it != m.odes.cend(); it++)
    {
      out << "|   |   d[" << it->first
          << "]/dt = " << pdrh::node_to_string_prefix(it->second) << endl;
    }
    out << "|   JUMPS:" << endl;
    for (pdrh::mode::jump j : m.jumps)
    {
      out << "|   |   GUARD: " << pdrh::node_to_string_prefix(j.guard) << endl;
      out << "|   |   SUCCESSOR: " << j.next_id << endl;
      out << "|   |   RESETS:" << endl;
      for (auto it = j.reset.cbegin(); it != j.reset.cend(); it++)
      {
        out << "|   |   |   " << it->first
            << " := " << pdrh::node_to_string_prefix(it->second) << endl;
      }
      out << "|   |   RESETS NONDET:" << endl;
      for (auto it = j.reset_nondet.cbegin(); it != j.reset_nondet.cend(); it++)
      {
        out << "|   |   |   " << it->first << " := ["
            << pdrh::node_to_string_prefix(it->second.first) << ", "
            << pdrh::node_to_string_prefix(it->second.second) << "]" << endl;
      }
      out << "|   |   RESETS RV:" << endl;
      for (auto it = j.reset_rv.cbegin(); it != j.reset_rv.cend(); it++)
      {
        out << "|   |   " << get<0>(it->second) << "   |   "
            << pdrh::node_to_string_infix(get<1>(it->second)) << "  | "
            << pdrh::node_to_string_prefix(get<2>(it->second)) << " |   "
            << pdrh::node_to_string_prefix(get<3>(it->second)) << "    |   "
            << pdrh::node_to_string_prefix(get<4>(it->second)) << endl;
      }
      out << "|   |   RESETS DD:" << endl;
      for (auto it = j.reset_dd.cbegin(); it != j.reset_dd.cend(); it++)
      {
        out << "|   |   |   dd(" << it->first << ") = (";
        for (auto it2 = it->second.cbegin(); it2 != it->second.cend(); it2++)
        {
          out << pdrh::node_to_string_prefix(it2->first) << " : "
              << pdrh::node_to_string_prefix(it2->second) << ", ";
        }
        out << ")" << endl;
      }
    }
  }
  out << "INIT:" << endl;
  for (pdrh::state s : pdrh::init)
  {
    out << "|   MODE: " << s.id << endl;
    out << "|   PROPOSITION: " << pdrh::node_to_string_prefix(s.prop) << endl;
  }
  if (pdrh::goal.size() > 0)
  {
    out << "GOAL:" << endl;
    for (pdrh::state s : pdrh::goal)
    {
      out << "|   MODE: " << s.id << endl;
      out << "|   PROPOSITION: " << pdrh::node_to_string_prefix(s.prop) << endl;
    }
  }
  else
  {
    out << "SYNTHESIZE:" << endl;
    for (auto it = pdrh::syn_map.cbegin(); it != pdrh::syn_map.cend(); it++)
    {
      out << "|   " << it->first << " "
          << pdrh::node_to_string_prefix(it->second) << endl;
    }
  }
  return out.str();
}

// getting string representation of the jump
string pdrh::print_jump(mode::jump j)
{
  stringstream out;
  out << j.guard << " ==>  @" << j.next_id << endl;
  return out.str();
}

/**
 * Translates an initial state specified as (and (x1 = v1) ... (xn = vn)) into map<string, double>
 *
 * @param init
 * @return
 */
std::map<std::string, double> pdrh::init_to_map(pdrh::state init)
{
  node *prop = init.prop;
  // checking if init is a conjunction of assignments
  if (prop->value != "and")
  {
    cerr << "could not translate init into a map: the outer operation is not "
            "an \"and\""
         << endl;
    exit(EXIT_FAILURE);
  }
  // setting up some auxiliary variables
  map<string, double> res;
  res[".mode"] = init.id;
  res[".time"] = 0;
  res[".step"] = 0;
  res[".global_time"] = 0;
  // parsing the assignments in the init
  for (node *n : prop->operands)
  {
    if (n->value != ("="))
    {
      cerr << "could not translate init into a map: on of the operations is "
              "not an \"=\""
           << endl;
      exit(EXIT_FAILURE);
    }
    res[node_to_string_infix(n->operands.front())] =
      node_to_double(n->operands.back());
  }
  return res;
}

vector<pdrh::mode *> pdrh::get_psy_path(
  map<string, vector<pair<pdrh::node *, pdrh::node *>>> time_series)
{
  std::vector<pdrh::mode *> path;
  path.push_back(pdrh::get_mode(pdrh::init.front().id));
  for (int i = 1; i < time_series.cbegin()->second.size(); i++)
  {
    if (
      pdrh::node_to_string_prefix(time_series["Mode"].at(i).first) !=
      pdrh::node_to_string_prefix(time_series["Mode"].at(i - 1).first))
    {
      istringstream is(
        pdrh::node_to_string_prefix(time_series["Mode"].at(i).first));
      int id;
      is >> id;
      path.push_back(pdrh::get_mode(id));
    }
  }
  return path;
}

void pdrh::distribution::push_uniform(string var, pdrh::node *a, pdrh::node *b)
{
  pdrh::distribution::uniform.insert(make_pair(var, make_pair(a, b)));
}

void pdrh::distribution::push_normal(
  string var,
  pdrh::node *mu,
  pdrh::node *sigma)
{
  pdrh::distribution::normal.insert(make_pair(var, make_pair(mu, sigma)));
}

void pdrh::distribution::push_gamma(string var, pdrh::node *a, pdrh::node *b)
{
  pdrh::distribution::gamma.insert(make_pair(var, make_pair(a, b)));
}

void pdrh::distribution::push_exp(string var, pdrh::node *lambda)
{
  pdrh::distribution::exp.insert(make_pair(var, lambda));
}

pdrh::node *pdrh::distribution::uniform_to_node(node *a, node *b)
{
  capd::interval support(
    pdrh::node_to_string_infix(a), pdrh::node_to_string_infix(b));
  capd::interval a_interval = pdrh2box::node_to_interval(a);
  capd::interval b_interval = pdrh2box::node_to_interval(b);
  // relaxing the bounds to account for rounding errors (temporary solution)
  double value_double =
    1 / ((b_interval.rightBound() + 1e-14) - (a_interval.leftBound() - 1e-14));
  return new node(value_double);
}

pdrh::node *
pdrh::distribution::normal_to_node(string var, node *mu, node *sigma)
{
  node *power_node_1 = new node("^", {sigma, new node("2")});
  node *mult_node_1 = new node("*", {new node("2"), power_node_1});
  node *minus_node = new node("-", {new node(var), mu});
  node *power_node_2 = new node("^", {minus_node, new node("2")});
  node *divide_node_1 = new node("/", {power_node_2, mult_node_1});
  node *unary_minus_node = new node("-", {divide_node_1});
  node *exp_node = new node("exp", {unary_minus_node});
  node *mult_node_2 = new node("*", {new node("2"), new node("3.14159265359")});
  node *sqrt_node = new node("sqrt", {mult_node_2});
  node *mult_node_3 = new node("*", {sigma, sqrt_node});
  node *divide_node_2 = new node("/", {new node("1"), mult_node_3});
  return new node("*", {exp_node, divide_node_2});
}

pdrh::node *pdrh::distribution::exp_to_node(string var, node *lambda)
{
  pdrh::node *times_node = new node("*", {lambda, new node(var)});
  pdrh::node *unary_minus_node = new node("-", {times_node});
  pdrh::node *exp_node = new node("exp", {unary_minus_node});
  return new node("*", {exp_node, lambda});
}

void pdrh::set_model_type()
{
  if (
    pdrh::rv_map.empty() && pdrh::dd_map.empty() && pdrh::par_map.empty() &&
    pdrh::syn_map.empty())
  {
    pdrh::model_type = pdrh::type::HA;
  }
  else if (
    pdrh::rv_map.empty() && pdrh::dd_map.empty() && pdrh::par_map.empty())
  {
    pdrh::model_type = pdrh::type::PSY;
  }
  else if (pdrh::par_map.empty())
  {
    pdrh::model_type = pdrh::type::PHA;
  }
  else
  {
    pdrh::model_type = pdrh::type::NPHA;
  }
}

/**
 * Outputs trajectory into a stream
 *
 * @param traj
 * @param os
 */
void pdrh::output_traj(
  std::vector<std::map<std::string, double>> traj,
  std::ostream &os)
{
  os << "[" << endl;
  // outputting the path into the file
  for (map<string, double> val : traj)
  {
    os << "{" << endl;
    for (auto it = val.begin(); it != val.end(); it++)
    {
      os << "\"" << it->first << "\" : " << it->second;
      if (it != prev(val.end()))
        os << ",";
      os << endl;
    }
    os << "}";
    if (val != traj[traj.size() - 1])
      os << ",";
    os << endl;
  }
  os << "]" << endl;
}
