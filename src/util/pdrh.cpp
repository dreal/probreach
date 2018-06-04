//
// Created by fedor on 24/01/16.
//

#include "pdrh.h"
#include "pdrh_config.h"
#include <string.h>
#include <logging/easylogging++.h>

using namespace std;

pdrh::type pdrh::model_type;
pair<pdrh::node*, pdrh::node*> pdrh::time;
map<string, tuple<pdrh::node*, pdrh::node*, pdrh::node*, pdrh::node*>> pdrh::rv_map;
map<string, string> pdrh::rv_type_map;
map<string, map<pdrh::node*, pdrh::node*>> pdrh::dd_map;
map<string, pair<pdrh::node*, pdrh::node*>> pdrh::var_map;
map<string, pair<pdrh::node*, pdrh::node*>> pdrh::par_map;
map<string, pdrh::node*> pdrh::syn_map;
vector<pdrh::mode> pdrh::modes;
vector<pdrh::state> pdrh::init;
vector<pdrh::state> pdrh::goal;
vector<vector<pdrh::mode*>> pdrh::paths;

map<string, pair<pdrh::node*, pdrh::node*>> pdrh::distribution::uniform;
map<string, pair<pdrh::node*, pdrh::node*>> pdrh::distribution::normal;
map<string, pdrh::node*> pdrh::distribution::exp;
map<string, pair<pdrh::node*, pdrh::node*>> pdrh::distribution::gamma;

// adding a variable
void pdrh::push_var(string var, pdrh::node* left, pdrh::node* right)
{
    // setting initial domain to (-infty, infty)
    capd::interval domain(-numeric_limits<double>::infinity(), numeric_limits<double>::infinity());
    if(strcmp(left->value.c_str(), "-infty") != 0)
    {
        domain.setLeftBound(pdrh::node_to_interval(left).leftBound());
    }
    if(strcmp(right->value.c_str(), "infty") != 0)
    {
        domain.setRightBound(pdrh::node_to_interval(right).rightBound());
    }
    // checking the width of the domain
    if(capd::intervals::width(domain) < 0)
    {
        stringstream s;
        s << "invalid domain " << domain << " for variable \"" << var << "\"";
        throw invalid_argument(s.str());
    }
    if(pdrh::var_map.find(var) != pdrh::var_map.cend())
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
void pdrh::push_time_bounds(pdrh::node* left, pdrh::node* right)
{
    capd::interval domain(pdrh::node_to_interval(left).leftBound(), pdrh::node_to_interval(right).rightBound());
    if(capd::intervals::width(domain) < 0)
    {
        stringstream s;
        s << "invalid time domain " << domain;
        throw invalid_argument(s.str());
    }
    pdrh::time = make_pair(left, right);
}

// adding invariant
void pdrh::push_invt(pdrh::mode& m, pdrh::node* invt)
{
    m.invts.push_back(invt);
}

// adding mode
void pdrh::push_mode(pdrh::mode m)
{
    vector<string> extra_vars = pdrh::get_keys_diff(pdrh::var_map, m.flow_map);
    for(string var : extra_vars)
    {
        m.flow_map.insert(make_pair(var, pdrh::var_map[var]));
        m.odes.insert(make_pair(var, pdrh::push_terminal_node("0")));
        // adding this variable to the list of parameters if it is not there yet,
        // if it is not a continuous or discrete random variable and
        // if its domain is an interval of length descending than 0.
        // There might be a problem as the length of the interval
        // is always descending than 0 due to overapproximation of
        // the interval arithmetics
        if(pdrh::par_map.find(var) == pdrh::par_map.cend() &&
                pdrh::rv_map.find(var) == pdrh::rv_map.cend() &&
                    pdrh::dd_map.find(var) == pdrh::dd_map.cend() &&
                        capd::intervals::width(capd::interval(
                                node_to_interval(pdrh::var_map[var].first).leftBound(),
                                node_to_interval(pdrh::var_map[var].second).rightBound())) > 0)
        {
            bool insert_flag = true;
            for(pdrh::mode md : pdrh::modes)
            {
                if(md.flow_map.find(var) != md.flow_map.cend())
                {
                    insert_flag = false;
                    break;
                }
            }
            if(insert_flag)
            {
                pdrh::par_map.insert(make_pair(var, pdrh::var_map[var]));
            }
        }
    }
    pdrh::modes.push_back(m);
}

// adding ode to the mode
void pdrh::push_ode(pdrh::mode& m, string var, pdrh::node* ode)
{
    if(pdrh::var_map.find(var) != pdrh::var_map.cend())
    {
        if(m.flow_map.find(var) == m.flow_map.cend())
        {
            m.flow_map.insert(make_pair(var, pdrh::var_map[var]));
            m.odes.insert(make_pair(var, ode));
            // removing a variable from the parameter list if there is an ode defined for it
            if(pdrh::par_map.find(var) != pdrh::par_map.cend())
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
        s << "variable \"" << var << "\" appears in the flow but it was not declared";
        throw invalid_argument(s.str());
    }
}

// adding a reset
void pdrh::push_reset(pdrh::mode& m, pdrh::mode::jump& j, string var, pdrh::node* expr)
{
    // implement error check
    j.reset.insert(make_pair(var, expr));
}

// adding a jump
void pdrh::push_jump(pdrh::mode& m, mode::jump j)
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
void pdrh::push_syn_pair(string var, pdrh::node* precision)
{
    pdrh::syn_map.insert(make_pair(var, precision));
}

// adding continuous random variable
void pdrh::push_rv(string var, pdrh::node* pdf, pdrh::node* left, pdrh::node* right, pdrh::node* start)
{
    pdrh::rv_map.insert(make_pair(var, make_tuple(pdf, left, right, start)));
}

// adding continuous random variable with its type
void pdrh::push_rv_type(string var, string type)
{
    pdrh::rv_type_map.insert(make_pair(var, type));
}

// adding discrete random variable
void pdrh::push_dd(string var, map<node*, node*> m)
{
    pdrh::dd_map.insert(make_pair(var, m));
}

// checking if the variable exists
bool pdrh::var_exists(string var)
{
    return (pdrh::var_map.find(var) != pdrh::var_map.cend());
}

// getting pointer to the mode by id
pdrh::mode* pdrh::get_mode(int id)
{
    for(int i = 0; i < pdrh::modes.size(); i++)
    {
        if(pdrh::modes.at(i).id == id)
        {
            return &pdrh::modes.at(i);
        }
    }
    return NULL;
}

// getting the shortest path between two modes
vector<pdrh::mode*> pdrh::get_shortest_path(pdrh::mode* begin, pdrh::mode* end)
{
    // initializing the set of paths
    vector<std::vector<pdrh::mode*>> paths;
    vector<pdrh::mode*> path;
    // checking if the initial state is the end state
    if(begin == end)
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
        while(!paths.empty())
        {
            // getting the first path in the set of paths
            path = paths.front();
            paths.erase(paths.cbegin());
            // getting the mode in the path
            pdrh::mode* cur_mode = path.back();
            vector<pdrh::mode*> successors = pdrh::get_successors(cur_mode);
            // proceeding if the current mode has successors
            if(!successors.empty())
            {
                // checking if one of the successors is the end mode
                if (std::find(successors.cbegin(), successors.cend(), end) != successors.cend())
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
                        if (find(path.cbegin(), path.cend(), suc_mode) == path.cend())
                        {
                            vector<pdrh::mode*> tmp_path = path;
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
vector<vector<pdrh::mode*>> pdrh::get_paths(pdrh::mode* begin, pdrh::mode* end, int path_length)
{
    // initializing the set of paths
    vector<std::vector<pdrh::mode*>> paths;
    vector<pdrh::mode*> path;
    path.push_back(begin);
    // initializing the stack
    vector<vector<pdrh::mode*>> stack;
    stack.push_back(path);
    while(!stack.empty())
    {
        // getting the first paths from the set of paths
        path = stack.front();
        stack.erase(stack.cbegin());
        // checking if the correct path of the required length is found
        if((path.back() == end) && (path.size() == path_length + 1))
        {
            paths.push_back(path);
        }
        // proceeding only if the length of the current path is ascending then the required length
        else if(path.size() < path_length + 1)
        {
            // getting the last mode in the path
            pdrh::mode* cur_mode = path.back();
            // getting the successors of the mode
            vector<pdrh::mode*> successors = pdrh::get_successors(cur_mode);
            for(pdrh::mode* suc_mode : successors)
            {
                // appending the successor the current paths
                vector<pdrh::mode*> new_path = path;
                new_path.push_back(suc_mode);
                // pushing the new path to the set of the paths
                stack.push_back(new_path);
            }
        }
    }
    return paths;
}

// getting all paths specified by the key word "paths:"
vector<vector<pdrh::mode*>> pdrh::get_paths()
{
    if(pdrh::paths.size() > 0)
    {
        return pdrh::paths;
    }
    else
    {
        return get_all_paths();
    }
}

// comparing two paths alphabetically
bool compare_paths_ascending(vector<pdrh::mode*> lhs, vector<pdrh::mode*> rhs)
{
    if(lhs.size() < rhs.size())
    {
        return true;
    }
    else if(lhs.size() > rhs.size())
    {
        return false;
    }
    else
    {
        stringstream s;
        for(pdrh::mode* m : lhs)
        {
            s << m->id;
        }
        string lstring = s.str();
        s.str("");
        for(pdrh::mode* m : rhs)
        {
            s << m->id;
        }
        if(lstring.compare(s.str()) <= 0)
        {
            return true;
        }
        return false;
    }
}

// getting all paths of length path_length for all combinations of init and goal modes
vector<vector<pdrh::mode*>> pdrh::get_all_paths(int path_length)
{
    vector<vector<pdrh::mode*>> res;
    for(pdrh::state i : pdrh::init)
    {
        for(pdrh::state g : pdrh::goal)
        {
            vector<vector<pdrh::mode*>> paths = pdrh::get_paths(pdrh::get_mode(i.id), pdrh::get_mode(g.id), path_length);
            res.insert(res.end(), paths.begin(), paths.end());
        }
    }
    // sorting all paths if the ascending order
    sort(res.begin(), res.end(), compare_paths_ascending);
    return res;
}

vector<vector<pdrh::mode*>> pdrh::get_all_paths()
{
    vector<vector<pdrh::mode*>> res;
    for(int i = global_config.reach_depth_min; i <= global_config.reach_depth_max; i++)
    {
        vector<vector<pdrh::mode*>> paths = pdrh::get_all_paths(i);
        res.insert(res.end(), paths.begin(), paths.end());
    }
    // sorting all paths if the ascending order
    sort(res.begin(), res.end(), compare_paths_ascending);
    return res;
}

// getting successors of the mode m
vector<pdrh::mode*> pdrh::get_successors(pdrh::mode* m)
{
    vector<pdrh::mode*> res;
    for(pdrh::mode::jump j : m->jumps)
    {
        pdrh::mode *tmp = pdrh::get_mode(j.next_id);
        if(tmp != NULL)
        {
            res.push_back(tmp);
        }
        else
        {
            stringstream s;
            s << "mode \"" << j.next_id << "\" is not defined but appears in the jump: " << pdrh::print_jump(j);
            throw invalid_argument(s.str());
        }
    }
    return res;
}

// getting initial modes
vector<pdrh::mode*> pdrh::get_init_modes()
{
    vector<pdrh::mode*> res;
    for(pdrh::state st : pdrh::init)
    {
        pdrh::mode *tmp = pdrh::get_mode(st.id);
        if(tmp != NULL)
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
vector<pdrh::mode*> pdrh::get_goal_modes()
{
    vector<pdrh::mode*> res;
    for(pdrh::state st : pdrh::goal)
    {
        pdrh::mode *tmp = pdrh::get_mode(st.id);
        if(tmp != NULL)
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
vector<string> pdrh::get_keys_diff(map<string, pair<pdrh::node*, pdrh::node*>> left, map<string, pair<pdrh::node*, pdrh::node*>> right)
{
    vector<string> res;
    for(auto it = left.cbegin(); it != left.cend(); it++)
    {
        if(right.find(it->first) == right.cend())
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
    for(auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
    {
        out << "|   " << it->first << " [" << pdrh::node_to_string_prefix(it->second.first) << ", " <<
                                                    pdrh::node_to_string_prefix(it->second.second) << "]" << endl;
    }
    out << "PARAMETERS:" << endl;
    for(auto it = pdrh::par_map.cbegin(); it != pdrh::par_map.cend(); it++)
    {
        out << "|   " << it->first << " [" << pdrh::node_to_string_prefix(it->second.first) << ", " <<
            pdrh::node_to_string_prefix(it->second.second) << "]" << endl;
    }
    out << "CONTINUOUS RANDOM VARIABLES:" << endl;
    for(auto it = pdrh::rv_map.cbegin(); it != pdrh::rv_map.cend(); it++)
    {
        out << "|   pdf(" << it->first << ") = " << pdrh::node_to_string_infix(get<0>(it->second)) << "  | "
                                                    << pdrh::node_to_string_prefix(get<1>(it->second)) << " |   "
                                                        << pdrh::node_to_string_prefix(get<2>(it->second)) << "    |   "
                                                            << pdrh::node_to_string_prefix(get<3>(it->second)) << endl;
    }
    out << "DISCRETE RANDOM VARIABLES:" << endl;
    for(auto it = pdrh::dd_map.cbegin(); it != pdrh::dd_map.cend(); it++)
    {
        out << "|   dd(" << it->first << ") = (";
        for(auto it2 = it->second.cbegin(); it2 != it->second.cend(); it2++)
        {
            cout << pdrh::node_to_string_prefix(it2->first) << " : " << pdrh::node_to_string_prefix(it2->second) << endl;
            out << pdrh::node_to_string_prefix(it2->first) << " : " << pdrh::node_to_string_prefix(it2->second) << ", ";
        }
        out << ")" << endl;
    }
    out << "TIME DOMAIN:" << endl;
    out << "|   [" << pdrh::node_to_string_prefix(pdrh::time.first) << ", " << pdrh::node_to_string_prefix(pdrh::time.second) << "]" << endl;
    out << "MODES:" << endl;
    for(pdrh::mode m : pdrh::modes)
    {
        out << "|   MODE: " << m.id << ";" << endl;
        out << "|   TIME DOMAIN: [" << pdrh::node_to_string_prefix(m.time.first) << ", " << pdrh::node_to_string_prefix(m.time.second) << "]" << endl;
        out << "|   INVARIANTS:" << endl;
        for(pdrh::node* n : m.invts)
        {
            out << "|   |   " << pdrh::node_to_string_prefix(n) << endl;
        }
        out << "|   FLOW_MAP:" << endl;
        for(auto it = m.flow_map.cbegin(); it != m.flow_map.cend(); it++)
        {
            out << "|   " << it->first << " " << " [" << pdrh::node_to_string_prefix(it->second.first) << ", " <<
                                                            pdrh::node_to_string_prefix(it->second.second) << "]" << endl;
        }
        out << "|   ODES:" << endl;
        for(auto it = m.odes.cbegin(); it != m.odes.cend(); it++)
        {
            out << "|   |   d[" << it->first << "]/dt = " << pdrh::node_to_string_prefix(it->second) << endl;
        }
        out << "|   JUMPS:" << endl;
        for(pdrh::mode::jump j : m.jumps)
        {
            out << "|   |   GUARD: " << pdrh::node_to_string_prefix(j.guard) << endl;
            out << "|   |   SUCCESSOR: " << j.next_id << endl;
            out << "|   |   RESETS:" << endl;
            for(auto it = j.reset.cbegin(); it != j.reset.cend(); it++)
            {
                out << "|   |   |   " << it->first << " := " << pdrh::node_to_string_prefix(it->second) << endl;
            }
            out << "|   |   RESETS NONDET:" << endl;
            for(auto it = j.reset_nondet.cbegin(); it != j.reset_nondet.cend(); it++)
            {
                out << "|   |   |   " << it->first << " := [" << pdrh::node_to_string_prefix(it->second.first) << ", "
                                                              << pdrh::node_to_string_prefix(it->second.second) << "]" << endl;
            }
            out << "|   |   RESETS RV:" << endl;
            for(auto it = j.reset_rv.cbegin(); it != j.reset_rv.cend(); it++)
            {
                out << "|   |   " << get<0>(it->second) << "   |   "
                    << pdrh::node_to_string_infix(get<1>(it->second)) << "  | "
                    << pdrh::node_to_string_prefix(get<2>(it->second)) << " |   "
                    << pdrh::node_to_string_prefix(get<3>(it->second)) << "    |   "
                    << pdrh::node_to_string_prefix(get<4>(it->second)) << endl;
            }
            out << "|   |   RESETS DD:" << endl;
            for(auto it = j.reset_dd.cbegin(); it != j.reset_dd.cend(); it++)
            {
                out << "|   |   |   dd(" << it->first << ") = (";
                for(auto it2 = it->second.cbegin(); it2 != it->second.cend(); it2++)
                {
                    cout << pdrh::node_to_string_prefix(it2->first) << " : " << pdrh::node_to_string_prefix(it2->second) << endl;
                    out << pdrh::node_to_string_prefix(it2->first) << " : " << pdrh::node_to_string_prefix(it2->second) << ", ";
                }
                out << ")" << endl;
            }
        }
    }
    out << "INIT:" << endl;
    for(pdrh::state s : pdrh::init)
    {
        out << "|   MODE: " << s.id << endl;
        out << "|   PROPOSITION: " << pdrh::node_to_string_prefix(s.prop) << endl;
    }
    if(pdrh::goal.size() > 0)
    {
        out << "GOAL:" << endl;
        for(pdrh::state s : pdrh::goal)
        {
            out << "|   MODE: " << s.id << endl;
            out << "|   PROPOSITION: " << pdrh::node_to_string_prefix(s.prop) << endl;
        }
    }
    else
    {
        out << "SYNTHESIZE:" << endl;
        for(auto it = pdrh::syn_map.cbegin(); it != pdrh::syn_map.cend(); it++)
        {
            out << "|   " << it->first << " " << pdrh::node_to_string_prefix(it->second) << endl;
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

// creating a terminal node
pdrh::node* pdrh::push_terminal_node(string value)
{
    pdrh::node* n = new pdrh::node(value);
    //n->value = value;
    return n;
}

// creating an operation node
pdrh::node* pdrh::push_operation_node(string value, vector<pdrh::node*> operands)
{
    pdrh::node* n = new pdrh::node(value, operands);
    //n->value = value;
    //n->operands = operands;
    return n;
}

// creating a terminal node
pdrh::node* pdrh::push_terminal_node(double value)
{
    stringstream s;
    s << value;

    pdrh::node* n = new pdrh::node(s.str());
    //n->value = s.str();
    return n;
}

// creating an operation node
pdrh::node* pdrh::push_operation_node(double value, vector<pdrh::node*> operands)
{
    stringstream s;
    s << value;

    pdrh::node* n = new pdrh::node(s.str(), operands);
    //n->value = s.str();
    //n->operands = operands;
    return n;
}

// getting a string representation of the node in prefix notation
string pdrh::node_to_string_prefix(pdrh::node* n)
{
    stringstream s;
    // checking whether n is an operation node
    if(n->operands.size() > 0)
    {
        s << "(" << n->value;
        for(pdrh::node* op : n->operands)
        {
            s << pdrh::node_to_string_prefix(op);
        }
        s << ")";
    }
    else
    {
        s  << " " << n->value;
    }
    return s.str();
}

// getting a string representation of the node in prefix notation with the fixed index
string pdrh::node_fix_index(pdrh::node* n, int step, string index)
{
    stringstream s;
    // checking whether n is an operation node
    if(n->operands.size() > 0)
    {
        s << "(" << n->value;
        for(pdrh::node* op : n->operands)
        {
            s << pdrh::node_fix_index(op, step, index);
        }
        s << ")";
    }
    else
    {
        s  << " " << n->value;
        if(pdrh::var_exists(n->value))
        {
            s  << "_" << step << "_" << index;
        }
    }
    return s.str();
}

// getting a string representation of the node in infix notation
string pdrh::node_to_string_infix(pdrh::node* n)
{
    stringstream s;
    // checking whether n is an operation node
    if(n->operands.size() > 1)
    {
        s << "(";
        for(int i = 0; i < n->operands.size() - 1; i++)
        {
            s << pdrh::node_to_string_infix(n->operands.at(i));
            s << n->value;
        }
        s << pdrh::node_to_string_infix(n->operands.at(n->operands.size() - 1)) << ")";
    }
    else if(n->operands.size() == 1)
    {
        if(strcmp(n->value.c_str(), "-") == 0)
        {
            s << "(" << n->value << pdrh::node_to_string_infix(n->operands.front()) << ")";
        }
        else
        {
            s << n->value << "(" << pdrh::node_to_string_infix(n->operands.front()) << ")";
        }
    }
    else
    {
        s << n->value;
    }
    return s.str();
}

// getting a string representation of reachability formula in smt2 format for all combinations of initial and goal modes
string pdrh::reach_to_smt2(vector<pdrh::mode*> path, vector<box> boxes)
{
    stringstream s;
    // setting logic
    s << "(set-logic QF_NRA_ODE)" << endl;
    // declaring variables and defining bounds
    for(auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
    {
        s << "(declare-fun " << it->first << " () Real)" << endl;
        for(int i = 0; i < path.size(); i++)
        {
            s << "(declare-fun " << it->first << "_" << i << "_0 () Real)" << endl;
            s << "(declare-fun " << it->first << "_" << i << "_t () Real)" << endl;
            if(strcmp(it->second.first->value.c_str(), "-infty") != 0)
            {
                s << "(assert (>= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
                s << "(assert (>= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
            }
            if(strcmp(it->second.second->value.c_str(), "infty") != 0)
            {
                s << "(assert (<= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
                s << "(assert (<= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
            }
        }
    }
    // declaring time pdrh::node_fix_index(reset_it->second, step, "t")
    for(int i = 0; i < path.size(); i++)
    {
        s << "(declare-fun time_" << i << " () Real)" << endl;
        s << "(assert (>= time_" << i << " " << pdrh::node_fix_index(path.at(i)->time.first, i, "0") << "))" << endl;
        s << "(assert (<= time_" << i << " " << pdrh::node_fix_index(path.at(i)->time.second, i, "0") << "))" << endl;
    }
    // defining odes
    for(auto path_it = path.cbegin(); path_it != path.cend(); path_it++)
    {
        if(find(path.cbegin(), path_it, *path_it) == path_it)
        {
            s << "(define-ode flow_" << (*path_it)->id << " (";
            for(auto ode_it = (*path_it)->odes.cbegin(); ode_it != (*path_it)->odes.cend(); ode_it++)
            {
                s << "(= d/dt[" << ode_it->first << "] " << pdrh::node_to_string_prefix(ode_it->second) << ")";
            }
            s << "))" << endl;
        }
    }
    // defining the reachability formula
    s << "(assert (and " << endl;
    // defining initial states
    s << "(or ";
    for(pdrh::state st : pdrh::init)
    {
        if(st.id == path.front()->id)
        {
            s << "(" << pdrh::node_fix_index(st.prop, 0, "0") << ")" << endl;
        }
    }
    s << ")" << endl;
    // defining boxes bounds
    for(box b : boxes)
    {
        map<string, capd::interval> m = b.get_map();
        for(int i = 0; i < path.size(); i++)
        {
            for (auto it = m.cbegin(); it != m.cend(); it++)
            {
                s << "(>= " << it->first << "_" << i << "_0 " << it->second.leftBound() << ")" << endl;
                s << "(<= " << it->first << "_" << i << "_0 " << it->second.rightBound() << ")" << endl;
                s << "(>= " << it->first << "_" << i << "_t " << it->second.leftBound() << ")" << endl;
                s << "(<= " << it->first << "_" << i << "_t " << it->second.rightBound() << ")" << endl;
            }
        }
    }
    // defining trajectory
    int step = 0;
    for(pdrh::mode* m : path)
    {
        // defining integrals
        s << "(= [";
        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
        {
            s << ode_it->first << "_" << step << "_t ";
        }
        s << "] (integral 0.0 time_" << step << " [";
        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
        {
            s << ode_it->first << "_" << step << "_0 ";
        }
        s << "] flow_" << m->id << "))" << endl;
        // defining invariants
        for(pdrh::node* invt : m->invts)
        {
            s << "(forall_t " << m->id << " [0.0 time_" << step << "] " << pdrh::node_fix_index(invt, step, "t") << ")" << endl;
        }
        // checking the current depth
        if(step < path.size() - 1)
        {
            // defining jumps
            for (pdrh::mode::jump j : m->jumps)
            {
                // only the jumps to the next mode in the path
                if(j.next_id == path.at(step+1)->id)
                {
                    s << pdrh::node_fix_index(j.guard, step, "t") << endl;
                    for (auto reset_it = j.reset.cbegin(); reset_it != j.reset.cend(); reset_it++)
                    {
                        s << "(= " << reset_it->first << "_" << step + 1 << "_0 " <<
                        pdrh::node_fix_index(reset_it->second, step, "t") << ")";
                    }
                }
            }
        }
        step++;
    }
    // defining goal
    s << "(or ";
    for(pdrh::state st : pdrh::goal)
    {
        if(st.id == path.back()->id)
        {
            s << "(" << pdrh::node_fix_index(st.prop, path.size() - 1, "t") << ")";
        }
    }
    s << ")))" << endl;
    // final statements
    s << "(check-sat)" << endl;
    s << "(exit)" << endl;
    return s.str();
}

// getting a string representation of reachability formula in smt2 format for the given initial and goal modes
/*
string pdrh::reach_to_smt2(pdrh::state init, pdrh::state goal, vector<pdrh::mode*> path, vector<box> boxes)
{
    stringstream s;
    // setting logic
    s << "(set-logic QF_NRA_ODE)" << endl;
    // declaring variables and defining bounds
    for(auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
    {
        s << "(declare-fun " << it->first << " () Real)" << endl;
        for(int i = 0; i < path.size(); i++)
        {
            s << "(declare-fun " << it->first << "_" << i << "_0 () Real)" << endl;
            s << "(declare-fun " << it->first << "_" << i << "_t () Real)" << endl;
            if(strcmp(it->second.first->value.c_str(), "-infty") != 0)
            {
                s << "(assert (>= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
                s << "(assert (>= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
            }
            if(strcmp(it->second.second->value.c_str(), "infty") != 0)
            {
                s << "(assert (<= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
                s << "(assert (<= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
            }
        }
    }
    // declaring time
    for(int i = 0; i < path.size(); i++)
    {
        s << "(declare-fun time_" << i << " () Real)" << endl;
        s << "(assert (>= time_" << i << " " << pdrh::node_to_string_prefix(path.at(i)->time.first) << "))" << endl;
        s << "(assert (<= time_" << i << " " << pdrh::node_to_string_prefix(path.at(i)->time.second) << "))" << endl;
    }
    // defining odes
    for(auto path_it = path.cbegin(); path_it != path.cend(); path_it++)
    {
        if(find(path.cbegin(), path_it, *path_it) == path_it)
        {
            s << "(define-ode flow_" << (*path_it)->id << " (";
            for(auto ode_it = (*path_it)->odes.cbegin(); ode_it != (*path_it)->odes.cend(); ode_it++)
            {
                s << "(= d/dt[" << ode_it->first << "] " << pdrh::node_to_string_prefix(ode_it->second) << ")";
            }
            s << "))" << endl;
        }
    }
    // defining the reachability formula
    s << "(assert (and " << endl;
    // defining initial states
    s << "(" << pdrh::node_fix_index(init.prop, 0, "0") << ")";
    // defining boxes bounds
    for(box b : boxes)
    {
        map<string, capd::interval> m = b.get_map();
        for(auto it = m.cbegin(); it != m.cend(); it++)
        {
            s << "(>= " << it->first << "_0_0 " << it->second.leftBound() << ")" << endl;
            s << "(<= " << it->first << "_0_0 " << it->second.rightBound() << ")" << endl;
        }
    }
    // defining trajectory
    int step = 0;
    for(pdrh::mode* m : path)
    {
        // defining integrals
        s << "(= [";
        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
        {
            s << ode_it->first << "_" << step << "_t ";
        }
        s << "] (integral 0.0 time_" << step << " [";
        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
        {
            s << ode_it->first << "_" << step << "_0 ";
        }
        s << "] flow_" << m->id << "))" << endl;
        // defining invariants
        for(pdrh::node* invt : m->invts)
        {
            s << "(forall_t " << m->id << " [0.0 time_" << step << "] " << pdrh::node_fix_index(invt, step, "t") << ")" << endl;
        }
        // checking the current depth
        if(step < path.size() - 1)
        {
            // defining jumps
            for (pdrh::mode::jump j : m->jumps)
            {
                s << pdrh::node_fix_index(j.guard, step, "t") << endl;
                for (auto reset_it = j.reset.cbegin(); reset_it != j.reset.cend(); reset_it++)
                {
                    s << "(= " << reset_it->first << "_" << step + 1 << "_0 " <<
                    pdrh::node_fix_index(reset_it->second, step, "t") << ")";
                }
            }
        }
        step++;
    }
    // defining goal
    s << "(" << pdrh::node_fix_index(goal.prop, path.size() - 1, "t") << ")))" << endl;
    // final statements
    s << "(check-sat)" << endl;
    s << "(exit)" << endl;
    return s.str();
}
*/

/*
string pdrh::reach_to_smt2_all_paths(vector<box> boxes)
{
    stringstream s;
    // setting logic
    s << "(set-logic QF_NRA_ODE)" << endl;
    // declaring variables and defining bounds
    for(auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
    {
        s << "(declare-fun " << it->first << " () Real)" << endl;
        for(int i = 0; i < path.size(); i++)
        {
            s << "(declare-fun " << it->first << "_" << i << "_0 () Real)" << endl;
            s << "(declare-fun " << it->first << "_" << i << "_t () Real)" << endl;
            if(strcmp(it->second.first->value.c_str(), "-infty") != 0)
            {
                s << "(assert (>= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
                s << "(assert (>= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
            }
            if(strcmp(it->second.second->value.c_str(), "infty") != 0)
            {
                s << "(assert (<= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
                s << "(assert (<= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
            }
        }
    }
    // declaring time
    for(int i = 0; i < path.size(); i++)
    {
        s << "(declare-fun time_" << i << " () Real)" << endl;
        s << "(assert (>= time_" << i << " " << pdrh::node_to_string_prefix(pdrh::time.first) << "))" << endl;
        s << "(assert (<= time_" << i << " " << pdrh::node_to_string_prefix(pdrh::time.second) << "))" << endl;
    }
    // defining odes
    for(auto path_it = path.cbegin(); path_it != path.cend(); path_it++)
    {
        if(find(path.cbegin(), path_it, *path_it) == path_it)
        {
            s << "(define-ode flow_" << (*path_it)->id << " (";
            for(auto ode_it = (*path_it)->odes.cbegin(); ode_it != (*path_it)->odes.cend(); ode_it++)
            {
                s << "(= d/dt[" << ode_it->first << "] " << pdrh::node_to_string_prefix(ode_it->second) << ")";
            }
            s << "))" << endl;
        }
    }
    // defining the reachability formula
    s << "(assert (and " << endl;
    // defining initial states
    s << "(or ";
    for(pdrh::state st : pdrh::init)
    {
        s << "(" << pdrh::node_fix_index(st.prop, 0, "0") << ")";
    }
    s << ")" << endl;
    // defining boxes bounds
    for(box b : boxes)
    {
        map<string, capd::interval> m = b.get_map();
        for(auto it = m.cbegin(); it != m.cend(); it++)
        {
            s << "(>= " << it->first << "_0_0 " << it->second.leftBound() << ")" << endl;
            s << "(<= " << it->first << "_0_0 " << it->second.rightBound() << ")" << endl;
        }
    }
    // defining trajectory
    int step = 0;
    for(pdrh::mode* m : path)
    {
        // defining integrals
        s << "(= [";
        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
        {
            s << ode_it->first << "_" << step << "_t ";
        }
        s << "] (integral 0.0 time_" << step << " [";
        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
        {
            s << ode_it->first << "_" << step << "_0 ";
        }
        s << "] flow_" << m->id << "))" << endl;
        // defining invariants
        for(pdrh::node* invt : m->invts)
        {
            s << "(forall_t " << m->id << " [0.0 time_" << step << "] " << pdrh::node_fix_index(invt, step, "t") << ")" << endl;
        }
        // checking the current depth
        if(step < path.size() - 1)
        {
            // defining jumps
            for (pdrh::mode::jump j : m->jumps)
            {
                // only the jumps to the next mode in the path
                if(j.next_id == path.at(step+1)->id)
                {
                    s << pdrh::node_fix_index(j.guard, step, "t") << endl;
                    for (auto reset_it = j.reset.cbegin(); reset_it != j.reset.cend(); reset_it++)
                    {
                        s << "(= " << reset_it->first << "_" << step + 1 << "_0 " <<
                        pdrh::node_fix_index(reset_it->second, step, "t") << ")";
                    }
                }
            }
        }
        step++;
    }
    // defining goal
    s << "(or ";
    for(pdrh::state st : pdrh::goal)
    {
        s << "(" << pdrh::node_fix_index(st.prop, path.size() - 1, "t") << ")";
    }
    s << ")))" << endl;
    // final statements
    s << "(check-sat)" << endl;
    s << "(exit)" << endl;
    return s.str();
}
*/

// USED
string pdrh::reach_c_to_smt2(vector<pdrh::mode*> path, vector<box> boxes)
{
    stringstream s;
    // setting logic
    s << "(set-logic QF_NRA_ODE)" << endl;
    // checking whether either of last jumps have a time node
//    pdrh::node* timed_node_neg;
//    for(pdrh::state st : pdrh::goal)
//    {
//        timed_node_neg = pdrh::get_time_node_neg(st.prop);
//        if(timed_node_neg)
//        {
//            break;
//        }
//    }
    // declaring variables and defining bounds
    for(auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
    {
        s << "(declare-fun " << it->first << " () Real)" << endl;
        for(int i = 0; i < path.size(); i++)
        {
            s << "(declare-fun " << it->first << "_" << i << "_0 () Real)" << endl;
            s << "(declare-fun " << it->first << "_" << i << "_t () Real)" << endl;
            if(strcmp(it->second.first->value.c_str(), "-infty") != 0)
            {
                s << "(assert (>= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
                s << "(assert (>= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
            }
            if(strcmp(it->second.second->value.c_str(), "infty") != 0)
            {
                s << "(assert (<= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
                s << "(assert (<= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
            }
        }
    }
    // declaring time
    for(int i = 0; i < path.size(); i++)
    {
        s << "(declare-fun time_" << i << " () Real)" << endl;
        s << "(assert (>= time_" << i << " " << pdrh::node_fix_index(path.at(i)->time.first, i, "0") << "))" << endl;
        s << "(assert (<= time_" << i << " " << pdrh::node_fix_index(path.at(i)->time.second, i, "0") << "))" << endl;
    }
    // declaring local time and bounds
    //if (!timed_node_neg)
    //{
        s << "(declare-fun local_time () Real)" << endl;
        for(unsigned long i = 0; i < path.size() - 1; i++)
        {
            s << "(declare-fun local_time_" << i << "_0 () Real)" << endl;
            s << "(declare-fun local_time_" << i << "_t () Real)" << endl;
            s << "(assert (= local_time_" << i << "_0 " << pdrh::node_fix_index(path.at(i)->time.first, i, "0") <<
            "))" << endl;
            s << "(assert (>= local_time_" << i << "_t " << pdrh::node_fix_index(path.at(i)->time.first, i, "0") <<
            "))" << endl;
            s << "(assert (<= local_time_" << i << "_t " << pdrh::node_fix_index(path.at(i)->time.second, i, "0") <<
            "))" << endl;
        }
        // last mode
        //s << "(declare-fun local_time () Real)" << endl;
        s << "(declare-fun local_time_" << path.size() - 1 << "_0 () Real)" << endl;
        s << "(declare-fun local_time_" << path.size() - 1 << "_t () Real)" << endl;
        s << "(assert (= local_time_" << path.size() - 1 << "_0 " << pdrh::node_fix_index(path.back()->time.first, path.size() - 1, "0") <<
        "))" << endl;
        s << "(assert (>= local_time_" << path.size() - 1 << "_t " << pdrh::node_fix_index(path.back()->time.first, path.size() - 1, "0") <<
        "))" << endl;
        s << "(assert (<= local_time_" << path.size() - 1 << "_t " << pdrh::node_fix_index(path.back()->time.second, path.size() - 1, "0") <<
        "))" << endl;
    //}
    // defining odes
    for(auto path_it = path.cbegin(); path_it != path.cend(); path_it++)
    {
        if(std::find(path.cbegin(), path_it, *path_it) == path_it)
        {
            s << "(define-ode flow_" << (*path_it)->id << " (";
            for(auto ode_it = (*path_it)->odes.cbegin(); ode_it != (*path_it)->odes.cend(); ode_it++)
            {
                s << "(= d/dt[" << ode_it->first << "] " << pdrh::node_to_string_prefix(ode_it->second) << ")";
            }
            // introducing local time if defined
            //if(!timed_node_neg)
            //{
                s << "(= d/dt[local_time] 1.0)";
            //}
            s << "))" << endl;
        }
    }
    // defining the negated reachability formula
    s << "(assert (and (and " << endl;
    // defining initial states
    s << "(or ";
    for(pdrh::state st : pdrh::init)
    {
        if(path.front()->id == st.id)
        {
            s << "(" << pdrh::node_fix_index(st.prop, 0, "0") << ")";
        }
    }
    s << ")" << endl;
    // defining boxes bounds
    for(box b : boxes)
    {
        map<string, capd::interval> m = b.get_map();
        for(int i = 0; i < path.size(); i++)
        {
            for (auto it = m.cbegin(); it != m.cend(); it++)
            {
                s << "(>= " << it->first << "_" << i << "_0 " << it->second.leftBound() << ")" << endl;
                s << "(<= " << it->first << "_" << i << "_0 " << it->second.rightBound() << ")" << endl;
                s << "(>= " << it->first << "_" << i << "_t " << it->second.leftBound() << ")" << endl;
                s << "(<= " << it->first << "_" << i << "_t " << it->second.rightBound() << ")" << endl;
            }
        }
    }
    // defining trajectory
    int step = 0;
    for(pdrh::mode* m : path)
    {
        // defining integrals
        s << "(= [";
        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
        {
            s << ode_it->first << "_" << step << "_t ";
        }
        // defining local time if enabled
        //if((step == path.size() - 1) && (!timed_node_neg))
        //if(!timed_node_neg)
        //{
            s << "local_time_" << step << "_t";
        //}
        s << "] (integral 0.0 time_" << step << " [";
        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
        {
            s << ode_it->first << "_" << step << "_0 ";
        }
        // defining local time if enabled
        //if((step == path.size() - 1) && (!timed_node_neg))
        //if(!timed_node_neg)
        //{
            s << "local_time_" << step << "_0";
        //}
        s << "] flow_" << m->id << "))" << endl;
        // defining invariants
        for(pdrh::node* invt : m->invts)
        {
            s << "(forall_t " << m->id << " [0.0 time_" << step << "] " << pdrh::node_fix_index(invt, step, "t") << ")" << endl;
        }
        // checking the current depth
        if(step < path.size() - 1)
        {
            // defining jumps
            for (pdrh::mode::jump j : m->jumps)
            {
                //cout << "Jumping from " << m->id << " to " << j.next_id << "(control " << path.at(step+1)->id << ")" << endl;
                if(j.next_id == path.at(step+1)->id)
                {
                    //cout << "Recording the jumping from " << m->id << " to " << j.next_id << "(control " << path.at(step+1)->id << ")" << endl;
                    s << pdrh::node_fix_index(j.guard, step, "t") << endl;
                    if (step < path.size() - 1)
                    {
                        for (auto reset_it = j.reset.cbegin(); reset_it != j.reset.cend(); reset_it++)
                        {
                            s << "(= " << reset_it->first << "_" << step + 1 << "_0 " <<
                            pdrh::node_fix_index(reset_it->second, step, "t") << ")";
                        }
                    }
                }
            }
        }
        step++;
    }
    s << ")";
    // defining goal
    s << "(and ";
    for(pdrh::state st : pdrh::goal)
    {
        if(path.back()->id == st.id)
        {
            pdrh::node* timed_node_neg = pdrh::get_time_node_neg(st.prop);
            if(!timed_node_neg)
            {
                // checking if there is a not in front of the guard predicate because dReal does not work nicely
                // with double negation
                s << "(= local_time_" << path.size() - 1 << "_t " << pdrh::node_fix_index(path.back()->time.second, path.size() - 1, "0") <<
                  ")" << endl;
                if(st.prop->value == "not")
                {
                    s << "(forall_t " << st.id << " [0 time_" << path.size() - 1 << "] (" <<
                    pdrh::node_fix_index(st.prop->operands.front(), path.size() - 1, "t") << "))";
                }
                // transforming the negation of disjunction into the conjunction of negations
                else if(st.prop->value == "or")
                {
                    for(pdrh::node* n : st.prop->operands)
                    {
                        s << "(forall_t " << st.id << " [0 time_" << path.size() - 1 << "] (not " <<
                        pdrh::node_fix_index(n, path.size() - 1, "t") << "))";
                    }
                }
                else
                {
                    s << "(forall_t " << st.id << " [0 time_" << path.size() - 1 << "] (not " << pdrh::node_fix_index(st.prop, path.size() - 1, "t") << "))";
                }
            }
            else
            {
                s << pdrh::node_fix_index(timed_node_neg, path.size() - 1, "t");
                delete timed_node_neg;
            }
        }
    }
    s << ")))" << endl;
    // final statements
    s << "(check-sat)" << endl;
    s << "(exit)" << endl;
    return s.str();
}

/*
string pdrh::reach_c_to_smt2(pdrh::state init, pdrh::state goal, vector<pdrh::mode*> path, vector<box> boxes)
{
    stringstream s;
    // setting logic
    s << "(set-logic QF_NRA_ODE)" << endl;
    // checking whether either of last jumps have a time node
    pdrh::node* timed_node_neg;
    timed_node_neg = pdrh::get_time_node_neg(goal.prop);
    // declaring local time and bounds
    if (!timed_node_neg)
    {
        for(int i = 0; i < path.size(); i++)
        {
            s << "(declare-fun local_time () Real)" << endl;
            s << "(declare-fun local_time_" << i << "_0 () Real)" << endl;
            s << "(declare-fun local_time_" << i << "_t () Real)" << endl;
            s << "(assert (= local_time_" << i << "_0 " << pdrh::node_to_string_prefix(pdrh::time.first) <<
            "))" << endl;
            s << "(assert (>= local_time_" << i << "_t " << pdrh::node_to_string_prefix(pdrh::time.first) <<
            "))" << endl;
            s << "(assert (<= local_time_" << i << "_t " << pdrh::node_to_string_prefix(pdrh::time.second) <<
            "))" << endl;
        }
        // last mode
        s << "(declare-fun local_time () Real)" << endl;
        s << "(declare-fun local_time_" << path.size() << "_0 () Real)" << endl;
        s << "(declare-fun local_time_" << path.size() << "_t () Real)" << endl;
        s << "(assert (= local_time_" << path.size() << "_0 " << pdrh::node_to_string_prefix(pdrh::time.first) <<
        "))" << endl;
        s << "(assert (= local_time_" << path.size() << "_t " << pdrh::node_to_string_prefix(pdrh::time.second) <<
        "))" << endl;
    }
    // declaring variables and defining bounds
    for(auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
    {
        s << "(declare-fun " << it->first << " () Real)" << endl;
        for(int i = 0; i < path.size(); i++)
        {
            s << "(declare-fun " << it->first << "_" << i << "_0 () Real)" << endl;
            s << "(declare-fun " << it->first << "_" << i << "_t () Real)" << endl;
            if(strcmp(it->second.first->value.c_str(), "-infty") != 0)
            {
                s << "(assert (>= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
                s << "(assert (>= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
            }
            if(strcmp(it->second.second->value.c_str(), "infty") != 0)
            {
                s << "(assert (<= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
                s << "(assert (<= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
            }
        }
    }
    // declaring time
    for(int i = 0; i < path.size(); i++)
    {
        s << "(declare-fun time_" << i << " () Real)" << endl;
        s << "(assert (>= time_" << i << " " << pdrh::node_to_string_prefix(pdrh::time.first) << "))" << endl;
        s << "(assert (<= time_" << i << " " << pdrh::node_to_string_prefix(pdrh::time.second) << "))" << endl;
    }
    // defining odes
    for(auto path_it = path.cbegin(); path_it != path.cend(); path_it++)
    {
        if(std::find(path.cbegin(), path_it, *path_it) == path_it)
        {
            s << "(define-ode flow_" << (*path_it)->id << " (";
            for(auto ode_it = (*path_it)->odes.cbegin(); ode_it != (*path_it)->odes.cend(); ode_it++)
            {
                s << "(= d/dt[" << ode_it->first << "] " << pdrh::node_to_string_prefix(ode_it->second) << ")";
            }
            // introducing local time if defined
            if(!timed_node_neg)
            {
                s << "(= d/dt[local_time] 1.0)";
            }
            s << "))" << endl;
        }
    }
    // defining the negated reachability formula
    s << "(assert (and (and " << endl;
    // defining initial states
    s << "(" << pdrh::node_fix_index(init.prop, 0, "0") << ")" << endl;
    // defining boxes bounds
    for(box b : boxes)
    {
        std::map<std::string, capd::interval> m = b.get_map();
        for(auto it = m.cbegin(); it != m.cend(); it++)
        {
            s << "(>= " << it->first << "_0_0 " << it->second.leftBound() << ")" << endl;
            s << "(<= " << it->first << "_0_0 " << it->second.rightBound() << ")" << endl;
        }
    }
    // defining trajectory
    int step = 0;
    for(pdrh::mode* m : path)
    {
        // defining integrals
        s << "(= [";
        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
        {
            s << ode_it->first << "_" << step << "_t ";
        }
        // defining local time if enabled
        if((step == path.size() - 1) && (!timed_node_neg))
        {
            s << "local_time_" << step << "_t";
        }
        s << "] (integral 0.0 time_" << step << " [";
        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
        {
            s << ode_it->first << "_" << step << "_0 ";
        }
        // defining local time if enabled
        if((step == path.size() - 1) && (!timed_node_neg))
        {
            s << "local_time_" << step << "_0";
        }
        s << "] flow_" << m->id << "))" << endl;
        // defining invariants
        for(pdrh::node* invt : m->invts)
        {
            s << "(forall_t " << m->id << " [0.0 time_" << step << "] " << pdrh::node_fix_index(invt, step, "t") << ")" << endl;
        }
        // checking the current depth
        if(step < path.size() - 1)
        {
            // defining jumps
            for (pdrh::mode::jump j : m->jumps)
            {
                s << pdrh::node_fix_index(j.guard, step, "t") << endl;
                if(step < path.size() - 1)
                {
                    for (auto reset_it = j.reset.cbegin(); reset_it != j.reset.cend(); reset_it++)
                    {
                        s << "(= " << reset_it->first << "_" << step + 1 << "_0 " <<
                        pdrh::node_fix_index(reset_it->second, step, "t") << ")";
                    }
                }
            }
        }
        step++;
    }
    s << ")";
    // defining goal
    if(!timed_node_neg)
    {
        s << "(forall_t " << goal.id << " [0 time_" << path.size() - 1 << "] (not " << pdrh::node_fix_index(goal.prop, path.size() - 1, "t") << "))";
    }
    else
    {
        s << pdrh::node_fix_index(timed_node_neg, path.size() - 1, "t");
        delete timed_node_neg;
    }
    s << "))" << endl;
    // final statements
    s << "(check-sat)" << endl;
    s << "(exit)" << endl;
    return s.str();
}
*/

// USED
string pdrh::reach_c_to_smt2(int depth, vector<pdrh::mode *> path, vector<box> boxes)
{
    if(depth == path.size() - 1)
    {
        return pdrh::reach_c_to_smt2(path, boxes);
    }
    else
    {
        stringstream s;
        // setting logic
        s << "(set-logic QF_NRA_ODE)" << endl;
        // checking whether either of last jumps have a time node
//        pdrh::node* timed_node_neg;
//        for(pdrh::mode::jump j : path.at(depth)->jumps)
//        {
//            timed_node_neg = pdrh::get_time_node_neg(j.guard);
//            if(timed_node_neg)
//            {
//                //cout << "Found timed node: " << pdrh::node_to_string_prefix(timed_node_neg) << endl;
//                break;
//            }
//        }
        // declaring variables and defining bounds
        for(auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
        {
            s << "(declare-fun " << it->first << " () Real)" << endl;
            for(int i = 0; i <= depth; i++)
            {
                s << "(declare-fun " << it->first << "_" << i << "_0 () Real)" << endl;
                s << "(declare-fun " << it->first << "_" << i << "_t () Real)" << endl;
                if(strcmp(it->second.first->value.c_str(), "-infty") != 0)
                {
                    s << "(assert (>= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
                    s << "(assert (>= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
                }
                if(strcmp(it->second.second->value.c_str(), "infty") != 0)
                {
                    s << "(assert (<= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
                    s << "(assert (<= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
                }
            }
        }
        // declaring time
        for(int i = 0; i <= depth; i++)
        {
            s << "(declare-fun time_" << i << " () Real)" << endl;
            s << "(assert (>= time_" << i << " " << pdrh::node_fix_index(path.at(i)->time.first, i, "0") << "))" << endl;
            s << "(assert (<= time_" << i << " " << pdrh::node_fix_index(path.at(i)->time.second, i, "0") << "))" << endl;
        }
        // declaring local time and bounds
//        if (!timed_node_neg)
//        {
            s << "(declare-fun local_time () Real)" << endl;
            //cout << "HERE" << endl;
            for(unsigned long i = 0; i < depth; i++)
            {
                s << "(declare-fun local_time_" << i << "_0 () Real)" << endl;
                s << "(declare-fun local_time_" << i << "_t () Real)" << endl;
                s << "(assert (= local_time_" << i << "_0 " << pdrh::node_fix_index(path.at(i)->time.first, i, "0") <<
                "))" << endl;
                s << "(assert (>= local_time_" << i << "_t " << pdrh::node_fix_index(path.at(i)->time.first, i, "0") <<
                "))" << endl;
                s << "(assert (<= local_time_" << i << "_t " << pdrh::node_fix_index(path.at(i)->time.second, i, "0") <<
                "))" << endl;
            }
            // last mode
            //s << "(declare-fun local_time () Real)" << endl;
            s << "(declare-fun local_time_" << depth << "_0 () Real)" << endl;
            s << "(declare-fun local_time_" << depth << "_t () Real)" << endl;
            s << "(assert (= local_time_" << depth << "_0 " << pdrh::node_fix_index(path.at(depth)->time.first, depth, "0") <<
            "))" << endl;
            s << "(assert (>= local_time_" << depth << "_t " << pdrh::node_fix_index(path.at(depth)->time.first, depth, "0") <<
            "))" << endl;
            s << "(assert (<= local_time_" << depth << "_t " << pdrh::node_fix_index(path.at(depth)->time.second, depth, "0") <<
            "))" << endl;
//        }
        // defining odes
        int step = 0;
        for(auto path_it = path.cbegin(); path_it != path.cend(); path_it++)
        {
            if(std::find(path.cbegin(), path_it, *path_it) == path_it)
            {
                s << "(define-ode flow_" << (*path_it)->id << " (";
                for(auto ode_it = (*path_it)->odes.cbegin(); ode_it != (*path_it)->odes.cend(); ode_it++)
                {
                    s << "(= d/dt[" << ode_it->first << "] " << pdrh::node_to_string_prefix(ode_it->second) << ")";
                }
                // introducing local time if defined
                //if((!timed_node_neg))
                //{
                    s << "(= d/dt[local_time] 1.0)";
                //}
                s << "))" << endl;
            }
            if(step >= depth)
            {
                break;
            }
            step++;
        }
        // defining the negated reachability formula
        s << "(assert (and (and " << endl;
        // defining initial states
        s << "(or ";
        for(pdrh::state st : pdrh::init)
        {
            if(path.front()->id == st.id)
            {
                s << "(" << pdrh::node_fix_index(st.prop, 0, "0") << ")";
            }
        }
        s << ")" << endl;
        // defining boxes bounds
        for(box b : boxes)
        {
            map<string, capd::interval> m = b.get_map();
            for(int i = 0; i <= depth; i++)
            {
                for (auto it = m.cbegin(); it != m.cend(); it++)
                {
                    s << "(>= " << it->first << "_" << i << "_0 " << it->second.leftBound() << ")" << endl;
                    s << "(<= " << it->first << "_" << i << "_0 " << it->second.rightBound() << ")" << endl;
                    s << "(>= " << it->first << "_" << i << "_t " << it->second.leftBound() << ")" << endl;
                    s << "(<= " << it->first << "_" << i << "_t " << it->second.rightBound() << ")" << endl;
                }
            }
        }
        // defining trajectory
        for(int i = 0; i <= depth; i++)
        {
            pdrh::mode* m = path.at(i);
            // defining integrals
            s << "(= [";
            for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
            {
                s << ode_it->first << "_" << i << "_t ";
            }
            // defining local time if enabled
            //if(!timed_node_neg)
            //{
                s << "local_time_" << i << "_t";
            //}
            s << "] (integral 0.0 time_" << i << " [";
            for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
            {
                s << ode_it->first << "_" << i << "_0 ";
            }
            // defining local time if enabled
            //if(!timed_node_neg)
            //{
                s << "local_time_" << i << "_0";
            //}
            s << "] flow_" << m->id << "))" << endl;
            // defining invariants
            for(pdrh::node* invt : m->invts)
            {
                s << "(forall_t " << m->id << " [0.0 time_" << i << "] " << pdrh::node_fix_index(invt, i, "t") << ")" << endl;
            }
            // checking the current depth
            if(i < depth)
            {
                // defining jumps
                for (pdrh::mode::jump j : m->jumps)
                {
                    // getting only the jumps leading to the next mode in the path
                    if(j.next_id == path.at(i+1)->id)
                    {
                        s << pdrh::node_fix_index(j.guard, i, "t") << endl;
                        if(i < path.size() - 1)
                        {
                            for (auto reset_it = j.reset.cbegin(); reset_it != j.reset.cend(); reset_it++)
                            {
                                s << "(= " << reset_it->first << "_" << i + 1 << "_0 " <<
                                pdrh::node_fix_index(reset_it->second, i, "t") << ")";
                            }
                        }
                    }
                }
            }
        }
        s << ")" << endl;
        // defining the last jump
        s << "(and ";
        for(pdrh::mode::jump j : path.at(depth)->jumps)
        {
            if(j.next_id == path.at(depth+1)->id)
            {
                pdrh::node* timed_node_neg = pdrh::get_time_node_neg(j.guard);
                if (!timed_node_neg)
                {
                    // checking if there is a not in front of the guard predicate because dReal does not work nicely
                    // with double negation
                    s << "(= local_time_" << depth << "_t " << pdrh::node_fix_index(path.at(depth)->time.second, depth, "0") <<
                      ")" << endl;
                    if(j.guard->value == "not")
                    {
                        /*
                        pdrh::node *guard_without_negation = new pdrh::node();
                        pdrh::copy_tree(guard_without_negation, j.guard->operands.front());
                        s << "(forall_t " << path.at(depth)->id << " [0 time_" << depth << "] (" <<
                        pdrh::node_fix_index(guard_without_negation, depth, "t") << "))";
                        delete guard_without_negation;
                        */
                        s << "(forall_t " << path.at(depth)->id << " [0 time_" << depth << "] (" <<
                        pdrh::node_fix_index(j.guard->operands.front(), depth, "t") << "))";
                    }
                    // transforming the negation of disjunction into the conjunction of negations
                    else if(j.guard->value == "or")
                    {
                        for(pdrh::node* n : j.guard->operands)
                        {
                            s << "(forall_t " << path.at(depth)->id << " [0 time_" << depth << "] (not " <<
                            pdrh::node_fix_index(n, depth, "t") << "))";
                        }
                    }
                    else
                    {
                        s << "(forall_t " << path.at(depth)->id << " [0 time_" << depth << "] (not " <<
                        pdrh::node_fix_index(j.guard, depth, "t") << "))";
                    }
                }
                else
                {
                    s << pdrh::node_fix_index(timed_node_neg, depth, "t");
                    delete timed_node_neg;
                }
            }
        }
        s << ")))" << endl;
        // asserting the time point for the last mode
        // final statements
        s << "(check-sat)" << endl;
        s << "(exit)" << endl;
        return s.str();
    }
}

/*
string pdrh::reach_c_to_smt2(pdrh::state init, pdrh::state goal, int depth, vector<pdrh::mode *> path, vector<box> boxes)
{
    if(depth == path.size() - 1)
    {
        return pdrh::reach_c_to_smt2(init, goal, path, boxes);
    }
    else
    {
        stringstream s;
        // setting logic
        s << "(set-logic QF_NRA_ODE)" << endl;
        // checking whether either of last jumps have a time node
        pdrh::node* timed_node_neg;
        for(pdrh::mode::jump j : path.at(depth)->jumps)
        {
            timed_node_neg = pdrh::get_time_node_neg(j.guard);
            if(timed_node_neg)
            {
                break;
            }
        }
        // declaring local time and bounds
        if (!timed_node_neg)
        {
            for(int i = 0; i <= depth; i++)
            {
                s << "(declare-fun local_time () Real)" << endl;
                s << "(declare-fun local_time_" << i << "_0 () Real)" << endl;
                s << "(declare-fun local_time_" << i << "_t () Real)" << endl;
                s << "(assert (= local_time_" << i << "_0 " << pdrh::node_to_string_prefix(pdrh::time.first) <<
                "))" << endl;
                s << "(assert (= local_time_" << i << "_t " << pdrh::node_to_string_prefix(pdrh::time.second) <<
                "))" << endl;
            }
        }
        // declaring variables and defining bounds
        for(auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
        {
            s << "(declare-fun " << it->first << " () Real)" << endl;
            for(int i = 0; i <= depth; i++)
            {
                s << "(declare-fun " << it->first << "_" << i << "_0 () Real)" << endl;
                s << "(declare-fun " << it->first << "_" << i << "_t () Real)" << endl;
                if(strcmp(it->second.first->value.c_str(), "-infty") != 0)
                {
                    s << "(assert (>= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
                    s << "(assert (>= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
                }
                if(strcmp(it->second.second->value.c_str(), "infty") != 0)
                {
                    s << "(assert (<= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
                    s << "(assert (<= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
                }
            }
        }
        // declaring time
        for(int i = 0; i <= depth; i++)
        {
            s << "(declare-fun time_" << i << " () Real)" << endl;
            s << "(assert (>= time_" << i << " " << pdrh::node_to_string_prefix(pdrh::time.first) << "))" << endl;
            s << "(assert (<= time_" << i << " " << pdrh::node_to_string_prefix(pdrh::time.second) << "))" << endl;
        }
        // defining odes
        int step = 0;
        for(auto path_it = path.cbegin(); path_it != path.cend(); path_it++)
        {
            if(std::find(path.cbegin(), path_it, *path_it) == path_it)
            {
                s << "(define-ode flow_" << (*path_it)->id << " (";
                for(auto ode_it = (*path_it)->odes.cbegin(); ode_it != (*path_it)->odes.cend(); ode_it++)
                {
                    s << "(= d/dt[" << ode_it->first << "] " << pdrh::node_to_string_prefix(ode_it->second) << ")";
                }
                // introducing local time if defined
                if((!timed_node_neg))
                {
                    s << "(= d/dt[local_time] 1.0)";
                }
                s << "))" << endl;
            }
            if(step >= depth)
            {
                break;
            }
            step++;
        }
        // defining the negated reachability formula
        s << "(assert (and (and " << endl;
        // defining initial states
        s << "(or ";
        for(pdrh::state st : pdrh::init)
        {
            if(path.front()->id == st.id)
            {
                s << "(" << pdrh::node_fix_index(st.prop, 0, "0") << ")";
            }
        }
        s << ")" << endl;
        // defining boxes bounds
        for(box b : boxes)
        {
            std::map<std::string, capd::interval> m = b.get_map();
            for(auto it = m.cbegin(); it != m.cend(); it++)
            {
                s << "(>= " << it->first << "_0_0 " << it->second.leftBound() << ")" << endl;
                s << "(<= " << it->first << "_0_0 " << it->second.rightBound() << ")" << endl;
            }
        }
        // defining trajectory
        for(int i = 0; i <= depth; i++)
        {
            pdrh::mode* m = path.at(i);
            // defining integrals
            s << "(= [";
            for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
            {
                s << ode_it->first << "_" << i << "_t ";
            }
            // defining local time if enabled
            if(!timed_node_neg)
            {
                s << "local_time_" << i << "_t";
            }
            s << "] (integral 0.0 time_" << i << " [";
            for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
            {
                s << ode_it->first << "_" << i << "_0 ";
            }
            // defining local time if enabled
            if(!timed_node_neg)
            {
                s << "local_time_" << i << "_0";
            }
            s << "] flow_" << m->id << "))" << endl;
            // defining invariants
            for(pdrh::node* invt : m->invts)
            {
                s << "(forall_t " << m->id << " [0.0 time_" << i << "] " << pdrh::node_fix_index(invt, i, "t") << ")" << endl;
            }
            // checking the current depth
            if(i < depth)
            {
                // defining jumps
                for (pdrh::mode::jump j : m->jumps)
                {
                    s << pdrh::node_fix_index(j.guard, i, "t") << endl;
                    if(i < path.size() - 1)
                    {
                        for (auto reset_it = j.reset.cbegin(); reset_it != j.reset.cend(); reset_it++)
                        {
                            s << "(= " << reset_it->first << "_" << i + 1 << "_0 " <<
                            pdrh::node_fix_index(reset_it->second, i, "t") << ")";
                        }
                    }
                }
            }
        }
        s << ")" << endl;
        // defining the last jump
        s << "(and ";
        for(pdrh::mode::jump j : path.at(depth)->jumps)
        {
            if(!timed_node_neg)
            {
                s << "(forall_t " << path.at(depth)->id << " [0 time_" << depth << "] (not " << pdrh::node_fix_index(j.guard, depth, "t") << "))";
            }
            else
            {
                s << pdrh::node_fix_index(timed_node_neg, depth, "t");
                delete timed_node_neg;
            }
        }
        s << ")))" << endl;
        // asserting the time point for the last mode
        // final statements
        s << "(check-sat)" << endl;
        s << "(exit)" << endl;
        return s.str();
    }
}
*/

// only works for statistical model checking
string pdrh::reach_to_isat(vector<box> boxes)
{
    // Generating variables declarations
    stringstream s;
    s << "DECL" << endl;
    // defining boolean variables
    s << "boole flow;" << endl;
    for(pdrh::mode md : pdrh::modes)
    {
        s << "boole mode_" << md.id << ";" << endl;
    }
    // defining variables
    map<string, pair<node*, node*>> vars = pdrh::var_map;
    for(auto it = vars.begin(); it != vars.end(); it++)
    {
        // printing only if the variable is not a nondeterministic or random parameter
        if(pdrh::par_map.find(it->first) == pdrh::par_map.end() &&
                pdrh::rv_map.find(it->first) == pdrh::rv_map.end() &&
                    pdrh::dd_map.find(it->first) == pdrh::dd_map.end())
        {
            s << "float [" << pdrh::node_to_string_infix(it->second.first) << ", " << pdrh::node_to_string_infix(it->second.second) << "] " << it->first << ";" << endl;
        }
    }
    // Defining the boxes
    for(box b : boxes)
    {
        map<string, capd::interval> edges = b.get_map();
        for(auto it = edges.begin(); it != edges.end(); it++)
        {
            s << "float [" << it->second.leftBound() << ", " << it->second.rightBound() << "] " << it->first << ";" << endl;
        }
    }

    // defining time and delta_time
    s << "float [" << pdrh::node_to_string_infix(pdrh::time.first) << ", " << (
            pdrh::node_to_interval(pdrh::time.second) * global_config.reach_depth_max).rightBound() << "] time;" << endl;
    s << "float [" << pdrh::node_to_string_infix(pdrh::time.first) << ", " << (
            pdrh::node_to_interval(pdrh::time.second) * global_config.reach_depth_max).rightBound() << "] delta_time;" << endl;

    // Generating init
    s << "INIT" << endl;
    s << "time=0;" << endl;
    s << "flow;" << endl;
    // Defining the boxes
    for(box b : boxes)
    {
        map<string, capd::interval> edges = b.get_map();
        for(auto it = edges.begin(); it != edges.end(); it++)
        {
            s << "(" << it->first << ">=" << it->second.leftBound() << ") and (" << it->first << "<=" << it->second.rightBound() << ");" << endl;
        }
    }
    s << "(" << endl;
    for(unsigned long i = 0; i < pdrh::init.size(); i++)
    {
        pdrh::state init = pdrh::init.at(i);
        // setting the discrete state
        s << "((mode_" << init.id << ")";
        for(pdrh::mode md : pdrh::modes)
        {
            if(md.id != init.id)
            {
                s << "and(!mode_" << md.id << ")";
            }
        }
        // generating assignment for continuous variables
        s << "and(" << pdrh::node_to_string_infix(init.prop) << "))" << endl;
        if(i < pdrh::init.size() - 1)
        {
            s << "or" << endl;
        }
    }
    s << ");" << endl;

    // Generating transitions
    s << "TRANS" << endl;
    // generating time transition
    s << "time' = time + delta_time;" << endl;
    // flow is followed by a jump
    s << "flow -> !flow';" << endl;
    // flow takes time
    s << "flow -> delta_time > 0;" << endl;
    // no mode changing inside the flow
    s << "flow -> ";
    for(unsigned long i = 0; i < pdrh::modes.size(); i++)
    {
        s << "(mode_" << pdrh::modes.at(i).id << " and mode_" << pdrh::modes.at(i).id << "')";
        if(i < pdrh::modes.size() - 1)
        {
            s << " or ";
        }
    }
    s << ";" << endl;
    // jump takes no time
    s << "!flow -> delta_time = 0;" << endl;
    // jump is followed by a flow
    s << "!flow -> flow';" << endl;

    // Generating code for modes (no invariants are currently supported)
    for(pdrh::mode md : pdrh::modes)
    {
        // generating odes
        map<string, node*> odes = md.odes;
        for(auto it = odes.begin(); it != odes.end(); it++)
        {
            s << "flow and mode_" << md.id << " -> (d." << it->first << " / d.time = " << pdrh::node_to_string_infix(it->second) << ");" << endl;
        }
        // generating invariants
        //for(pdrh::node* n : md.invts)
        //{
        //    s << n.to_infix("(time)");
        //}
        //generating jumps
        vector<pdrh::mode::jump> jumps = md.jumps;
        if(!jumps.empty())
        {
            s << "!flow and mode_" << md.id << " -> " << endl;
            s << "(" << endl;
            for(unsigned long i = 0; i < jumps.size(); i++)
            {
                s << "(";
                s << "(" << pdrh::node_to_string_infix(jumps.at(i).guard) << ") and (mode_" << jumps.at(i).next_id << "')";
                map<string, node*> reset = jumps.at(i).reset;
                for(auto it = reset.cbegin(); it != reset.cend(); it++)
                {
                    s << " and (" << it->first << "' = " << pdrh::node_to_string_infix(it->second) << ")";
                }
                s << ")" << endl;
                if(i < jumps.size() - 1)
                {
                    s << "or" << endl;
                }
            }
            s << ");" << endl;
        }
    }

    // Generating target
    s << "TARGET" << endl;
    s << "(" << endl;
    for(unsigned long i = 0; i < pdrh::goal.size(); i++)
    {
        pdrh::state goal = pdrh::goal.at(i);
        // setting the discrete state
        s << "((mode_" << goal.id << ")";
        for(pdrh::mode md : pdrh::modes)
        {
            if(md.id != goal.id)
            {
                s << "and(!mode_" << md.id << ")";
            }
        }
        // generating assignment for continuous variables
        s << "and(" << pdrh::node_to_string_infix(goal.prop) << "))" << endl;
        if(i < pdrh::goal.size() - 1)
        {
            s << "or" << endl;
        }
    }
    s << ");" << endl;

    return s.str();
}

// domain of nondeterministic parameters
box pdrh::get_nondet_domain()
{
    map<std::string, capd::interval> m;
    for(auto it = pdrh::par_map.cbegin(); it != pdrh::par_map.cend(); it++)
    {
        m.insert(make_pair(it->first, capd::interval(pdrh::node_to_interval(it->second.first).leftBound(),
                                                     pdrh::node_to_interval(it->second.second).rightBound())));
    }
    return box(m);
}

// domain of parameters to synthesize
box pdrh::get_psy_domain()
{
    map<std::string, capd::interval> m;
    for(auto it = pdrh::syn_map.cbegin(); it != pdrh::syn_map.cend(); it++)
    {
        m.insert(make_pair(it->first, capd::interval(pdrh::node_to_interval(pdrh::var_map[it->first].first).leftBound(),
                                                     pdrh::node_to_interval(pdrh::var_map[it->first].second).rightBound())));
    }
    return box(m);
}

/*
void pdrh::push_psy_goal(int mode_id, box b)
{
    pdrh::state st;
    st.id = mode_id;
    map<string, capd::interval> m = b.get_map();
    vector<pdrh::node*> operands;
    for(auto it = m.cbegin(); it != m.cend(); it++)
    {
        pdrh::node* var = pdrh::push_terminal_node(it->first);
        stringstream s;
        s << it->second.leftBound();
        pdrh::node* left_bound = pdrh::push_terminal_node(s.str());
        s.str("");
        s << it->second.rightBound();
        pdrh::node* right_bound = pdrh::push_terminal_node(s.str());
        s.str("");
        vector<pdrh::node*> tmp;
        tmp.push_back(var);
        tmp.push_back(left_bound);
        pdrh::node* left_constraint = pdrh::push_operation_node(">=", tmp);
        operands.push_back(left_constraint);
        tmp.clear();
        tmp.push_back(var);
        tmp.push_back(right_bound);
        pdrh::node* right_constraint = pdrh::push_operation_node("<=", tmp);
        operands.push_back(right_constraint);
        tmp.clear();
    }
    st.prop = pdrh::push_operation_node("and", operands);
    pdrh::goal = vector<pdrh::state>{ st };
    // updating time bounds
    pdrh::var_map.insert(make_pair("tau", make_pair(pdrh::push_operation_node("0"), m["tau"])));
    pdrh::push_time_bounds(pdrh::push_terminal_node("0"), m["tau"]);
}
*/
/*
void pdrh::push_psy_c_goal(int mode_id, box b)
{
    pdrh::state st;
    st.id = mode_id;
    std::map<std::string, capd::interval> m = b.get_map();
    std::vector<pdrh::node*> operands;
    for(auto it = m.cbegin(); it != m.cend(); it++)
    {
        // using everything except for time tau
        if(strcmp(it->first.c_str(), "tau") != 0)
        {
            pdrh::node *var = pdrh::push_terminal_node(it->first);
            std::stringstream s;
            s << it->second.leftBound();
            pdrh::node *left_bound = pdrh::push_terminal_node(s.str());
            s.str("");
            s << it->second.rightBound();
            pdrh::node *right_bound = pdrh::push_terminal_node(s.str());
            s.str("");
            std::vector<pdrh::node *> tmp;
            tmp.push_back(var);
            tmp.push_back(left_bound);
            pdrh::node *left_constraint = pdrh::push_operation_node("<", tmp);
            operands.push_back(left_constraint);
            tmp.clear();
            tmp.push_back(var);
            tmp.push_back(right_bound);
            pdrh::node *right_constraint = pdrh::push_operation_node(">", tmp);
            operands.push_back(right_constraint);
            tmp.clear();
        }
    }
    pdrh::node* or_node = pdrh::push_operation_node("or", operands);
    // adding time as a constraint
    std::stringstream s;
    s << m["tau"].leftBound();
    pdrh::node *left_time_bound = pdrh::push_operation_node("=", std::vector<pdrh::node*>{ pdrh::push_terminal_node("tau"), pdrh::push_terminal_node(s.str())});
    s.str("");
    //s << m["tau"].rightBound();
    //pdrh::node *right_time_bound = pdrh::push_operation_node("<=", std::vector<pdrh::node*>{ pdrh::push_terminal_node("tau"), pdrh::push_terminal_node(s.str())});
    //st.prop = pdrh::push_operation_node("and", std::vector<pdrh::node*>{left_time_bound, right_time_bound, or_node});
    st.prop = pdrh::push_operation_node("and", std::vector<pdrh::node*>{left_time_bound, or_node});
    pdrh::goal = std::vector<pdrh::state>{ st };
    // updating time bounds
    pdrh::var_map["tau"] = capd::interval(0, m["tau"].leftBound());
    pdrh::push_time_bounds(capd::interval(0, m["tau"].leftBound()));
}
*/

// mode, step, box
/*
vector<tuple<int, box>> pdrh::series_to_boxes(map<string, vector<capd::interval>> time_series)
{
    vector<std::tuple<int, box>> res;
    for(int i = 0; i < time_series.cbegin()->second.size(); i++)
    {
        map<string, capd::interval> m;
        for(auto it = time_series.cbegin(); it != time_series.cend(); it++)
        {
            if((strcmp(it->first.c_str(), "Mode") != 0) && (strcmp(it->first.c_str(), "Step") != 0))
            {
                if(strcmp(it->first.c_str(), "Time") == 0)
                {
                    m.insert(std::make_pair("tau", it->second.at(i)));
                }
                else
                {
                    m.insert(std::make_pair(it->first, it->second.at(i)));
                }
            }
        }
        res.push_back(std::make_tuple((int) time_series["Mode"].at(i).leftBound(), box(m)));
    }
    return res;
}
*/

/*
vector<pdrh::state> pdrh::series_to_goals(map<string, vector<pair<pdrh::node*, pdrh::node*>>> time_series)
{
    vector<pdrh::state> res;
    for(int i = 0; i < time_series.cbegin()->second.size(); i++)
    {
        pdrh::state goal;
        vector<pdrh::node*> operands;
        for(auto it = time_series.cbegin(); it != time_series.cend(); it++)
        {
            if(strcmp(it->first.c_str(), "Step") != 0)
            {
                if(strcmp(it->first.c_str(), "Mode") == 0)
                {
                    istringstream is(pdrh::node_to_string_prefix(it->second.at(i).first));
                    is >> goal.id;
                }
                else if(strcmp(it->first.c_str(), "Time") == 0)
                {
                    //pdrh::node* left_node = pdrh::push_operation_node(">=", {push_terminal_node(global_config.time_var_name), it->second.at(i).first});
                    //pdrh::node* right_node = pdrh::push_operation_node("<=", {push_terminal_node(global_config.time_var_name), it->second.at(i).second});
                    //operands.push_back(pdrh::push_operation_node("and", {left_node, right_node}));
                    operands.push_back(pdrh::push_operation_node("=", {push_terminal_node(global_config.time_var_name), it->second.at(i).first}));
                }
                else
                {
                    if(!pdrh::is_node_empty(it->second.at(i).first) &&
                            !pdrh::is_node_empty(it->second.at(i).second))
                    {
                        pdrh::node* left_node = pdrh::push_operation_node(">=", {push_terminal_node(it->first), it->second.at(i).first});
                        pdrh::node* right_node = pdrh::push_operation_node("<=", {push_terminal_node(it->first), it->second.at(i).second});
                        operands.push_back(pdrh::push_operation_node("and", {left_node, right_node}));
                    }
                }
            }
        }
        goal.prop = push_operation_node("and", operands);
        res.push_back(goal);
    }
    return res;
}
*/

vector<pdrh::mode*> pdrh::get_psy_path(map<string, vector<pair<pdrh::node*, pdrh::node*>>> time_series)
{
    std::vector<pdrh::mode*> path;
    path.push_back(pdrh::get_mode(pdrh::init.front().id));
    for(int i = 1; i < time_series.cbegin()->second.size(); i++)
    {
        if(pdrh::node_to_string_prefix(time_series["Mode"].at(i).first) != pdrh::node_to_string_prefix(time_series["Mode"].at(i-1).first))
        {
            istringstream is(pdrh::node_to_string_prefix(time_series["Mode"].at(i).first));
            int id;
            is >> id;
            path.push_back(pdrh::get_mode(id));
        }
    }
    return path;
}


/*
std::vector<pdrh::mode*> pdrh::get_psy_path(std::map<std::string, std::vector<capd::interval>> time_series)
{
    std::vector<pdrh::mode*> path;
    path.push_back(pdrh::get_mode(pdrh::init.front().id));
    for(int i = 1; i < time_series.cbegin()->second.size(); i++)
    {
        if(time_series["Mode"].at(i).leftBound() != time_series["Mode"].at(i - 1).leftBound())
        {
            path.push_back(pdrh::get_mode((int) time_series["Mode"].at(i).leftBound()));
        }
    }
    return path;
}
*/

pdrh::node* pdrh::get_first_time_node(pdrh::node * root)
{
    //cout << pdrh::node_to_string_prefix(root) << endl;
    if(root->operands.size() > 0)
    {
        if(strcmp(root->value.c_str(), "=") == 0)
        {
            for(pdrh::node* child : root->operands)
            {
                if(find(global_config.time_var_name.begin(), global_config.time_var_name.end(), child->value.c_str()) != global_config.time_var_name.end())
                {
                    return root;
                }
                else
                {
                    return pdrh::get_first_time_node(child);
                }
            }
        }
        else
        {
            for(pdrh::node* child : root->operands)
            {
                return pdrh::get_first_time_node(child);
            }
        }
    }
    return NULL;
}

void pdrh::get_first_time_node(node* root, node* time_node)
{
    //cout << "IN FUNCTION: " << pdrh::node_to_string_prefix(root) << " " << &root << endl;
    if(strcmp(root->value.c_str(), "=") == 0)
    {
        for(pdrh::node* child : root->operands)
        {
            if(find(global_config.time_var_name.begin(), global_config.time_var_name.end(), child->value.c_str()) != global_config.time_var_name.end())
            {
                *time_node = *root;
                root->value = "true";
                root->operands.clear();
            }
            else
            {
                pdrh::get_first_time_node(child, time_node);
            }
        }
    }
    else
    {
        for(pdrh::node* child : root->operands)
        {
            pdrh::get_first_time_node(child, time_node);
        }
    }
}

void pdrh::copy_tree(pdrh::node * &copy, pdrh::node * origin)
{
    copy->value = origin->value;
    for(pdrh::node* child : origin->operands)
    {
        pdrh::node* copy_operand = new pdrh::node;
        pdrh::copy_tree(copy_operand, child);
        copy->operands.push_back(copy_operand);
    }
}

bool pdrh::is_node_empty(node* n)
{
    return n->value.empty() && n->operands.empty();
}

pdrh::node* pdrh::get_time_node_neg(pdrh::node* root)
{
    pdrh::node *root_copy = new pdrh::node();
    pdrh::copy_tree(root_copy, root);
    pdrh::node* time_node = new pdrh::node;
    pdrh::get_first_time_node(root_copy, time_node);
    //cout << "Node before removing time node: " << pdrh::node_to_string_prefix(root) << endl;
    if(pdrh::is_node_empty(time_node))
    {
        return NULL;
    }
    // creating a negation node
    pdrh::node* not_node = pdrh::push_operation_node("not", vector<pdrh::node*>{root_copy});
    // creating a resulting node
    pdrh::node* res_node = pdrh::push_operation_node("and", vector<pdrh::node*>{time_node, not_node});
    //cout << "RES TIME NODE: " << pdrh::node_to_string_prefix(res_node) << endl;
    return res_node;
}

// throws exception in case if one of the terminal modes is not a number
// evaluates the value of arithmetic expression
capd::interval pdrh::node_to_interval(pdrh::node *expr)
{
    if(expr->operands.size() == 0)
    {
        return capd::interval(expr->value, expr->value);
    }
    else if(expr->operands.size() > 2)
    {
        CLOG(ERROR, "model") << "The number of operands can't be descending than 2";
        exit(EXIT_FAILURE);
    }
    else
    {
        if(strcmp(expr->value.c_str(), "+") == 0)
        {
            if(expr->operands.size() == 1)
            {
                return pdrh::node_to_interval(expr->operands.front());
            }
            else if(expr->operands.size() == 2)
            {
                return pdrh::node_to_interval(expr->operands.front()) +
                        pdrh::node_to_interval(expr->operands.back());
            }
        }
        else if(strcmp(expr->value.c_str(), "-") == 0)
        {
            if(expr->operands.size() == 1)
            {
                return capd::interval(-1.0) * pdrh::node_to_interval(expr->operands.front());
            }
            else if(expr->operands.size() == 2)
            {
                return pdrh::node_to_interval(expr->operands.front()) -
                        pdrh::node_to_interval(expr->operands.back());
            }
        }
        else if(strcmp(expr->value.c_str(), "*") == 0)
        {
            return pdrh::node_to_interval(expr->operands.front()) *
                    pdrh::node_to_interval(expr->operands.back());
        }
        else if(strcmp(expr->value.c_str(), "/") == 0)
        {
            return pdrh::node_to_interval(expr->operands.front()) /
                    pdrh::node_to_interval(expr->operands.back());
        }
        else if(strcmp(expr->value.c_str(), "^") == 0)
        {
            return capd::intervals::power(pdrh::node_to_interval(expr->operands.front()),
                                          pdrh::node_to_interval(expr->operands.back()));
        }
        else if(strcmp(expr->value.c_str(), "sqrt") == 0)
        {
            return capd::intervals::sqrt(pdrh::node_to_interval(expr->operands.front()));
        }
        else if(strcmp(expr->value.c_str(), "abs") == 0)
        {
            return capd::intervals::iabs(pdrh::node_to_interval(expr->operands.front()));
        }
        else if(strcmp(expr->value.c_str(), "exp") == 0)
        {
            return capd::intervals::exp(pdrh::node_to_interval(expr->operands.front()));
        }
        else if(strcmp(expr->value.c_str(), "log") == 0)
        {
            return capd::intervals::log(pdrh::node_to_interval(expr->operands.front()));
        }
        else if(strcmp(expr->value.c_str(), "sin") == 0)
        {
            return capd::intervals::sin(pdrh::node_to_interval(expr->operands.front()));
        }
        else if(strcmp(expr->value.c_str(), "cos") == 0)
        {
            return capd::intervals::cos(pdrh::node_to_interval(expr->operands.front()));
        }
        else if(strcmp(expr->value.c_str(), "tan") == 0)
        {
            return capd::intervals::tan(pdrh::node_to_interval(expr->operands.front()));
        }
        else if(strcmp(expr->value.c_str(), "asin") == 0)
        {
            return capd::intervals::asin(pdrh::node_to_interval(expr->operands.front()));
        }
        else if(strcmp(expr->value.c_str(), "acos") == 0)
        {
            return capd::intervals::acos(pdrh::node_to_interval(expr->operands.front()));
        }
        else if(strcmp(expr->value.c_str(), "atan") == 0)
        {
            return capd::intervals::atan(pdrh::node_to_interval(expr->operands.front()));
        }
        else
        {
            CLOG(ERROR, "model") << "Unknown function \"" << expr->value << "\"";
            exit(EXIT_FAILURE);
        }
    }
}

void pdrh::distribution::push_uniform(string var, pdrh::node* a, pdrh::node* b)
{
    pdrh::distribution::uniform.insert(make_pair(var, make_pair(a, b)));
}

void pdrh::distribution::push_normal(string var, pdrh::node* mu, pdrh::node* sigma)
{
    pdrh::distribution::normal.insert(make_pair(var, make_pair(mu, sigma)));
}

void pdrh::distribution::push_gamma(string var, pdrh::node* a, pdrh::node* b)
{
    pdrh::distribution::gamma.insert(make_pair(var, make_pair(a, b)));
}

void pdrh::distribution::push_exp(string var, pdrh::node* lambda)
{
    pdrh::distribution::exp.insert(make_pair(var, lambda));
}

pdrh::node* pdrh::distribution::uniform_to_node(node* a, node* b)
{
    pdrh::node* n1 = pdrh::push_terminal_node("1");
    pdrh::node* op1 = pdrh::push_operation_node("-", vector<pdrh::node*>{b, a});
    return pdrh::push_operation_node("/", vector<pdrh::node*>{n1, op1});
}

pdrh::node* pdrh::distribution::normal_to_node(string var, node* mu, node* sigma)
{
    pdrh::node* power_node_1 = pdrh::push_operation_node("^", vector<pdrh::node*>{sigma, pdrh::push_terminal_node("2")});
    pdrh::node* mult_node_1 = pdrh::push_operation_node("*", vector<pdrh::node*>{pdrh::push_terminal_node("2"), power_node_1});
    pdrh::node* minus_node = pdrh::push_operation_node("-", vector<pdrh::node*>{pdrh::push_terminal_node(var), mu});
    pdrh::node* power_node_2 = pdrh::push_operation_node("^", vector<pdrh::node*>{minus_node, pdrh::push_terminal_node("2")});
    pdrh::node* divide_node_1 = pdrh::push_operation_node("/", vector<pdrh::node*>{power_node_2, mult_node_1});
    pdrh::node* unary_minus_node = pdrh::push_operation_node("-", vector<pdrh::node*>{divide_node_1});
    pdrh::node* exp_node = pdrh::push_operation_node("exp", vector<pdrh::node*>{unary_minus_node});
    pdrh::node* mult_node_2 = pdrh::push_operation_node("*", vector<pdrh::node*>{pdrh::push_terminal_node("2"),
                                                                                 pdrh::push_terminal_node("3.14159265359")});
    pdrh::node* sqrt_node = pdrh::push_operation_node("sqrt", vector<pdrh::node*>{mult_node_2});
    pdrh::node* mult_node_3 = pdrh::push_operation_node("*", vector<pdrh::node*>{sigma, sqrt_node});
    pdrh::node* divide_node_2 = pdrh::push_operation_node("/", vector<pdrh::node*>{pdrh::push_terminal_node("1"), mult_node_3});
    return pdrh::push_operation_node("*", vector<pdrh::node*>{exp_node, divide_node_2});
}

pdrh::node* pdrh::distribution::exp_to_node(string var, node* lambda)
{
    pdrh::node* plus_node = pdrh::push_operation_node("+", vector<pdrh::node*>{lambda, pdrh::push_terminal_node(var)});
    pdrh::node* unary_minus_node = pdrh::push_operation_node("-", vector<pdrh::node*>{plus_node});
    pdrh::node* exp_node = pdrh::push_operation_node("exp", vector<pdrh::node*>{unary_minus_node});
    return pdrh::push_operation_node("*", vector<pdrh::node*>{exp_node, lambda});
}

void pdrh::push_prob_partition_prec(string var, capd::interval prec)
{
    global_config.partition_prob_map.insert(make_pair(var, prec));
}

void pdrh::push_nondet_partition_prec(string var, capd::interval prec)
{
    global_config.partition_nondet_map.insert(make_pair(var, prec));
}

void pdrh::set_model_type()
{
    if(pdrh::rv_map.empty() && pdrh::dd_map.empty() && pdrh::par_map.empty() && pdrh::syn_map.empty())
    {
        pdrh::model_type = pdrh::type::HA;
        //pdrh::model_type = pdrh::type::NPHA;
    }
    else if(pdrh::rv_map.empty() && pdrh::dd_map.empty() && pdrh::par_map.empty())
    {
        pdrh::model_type = pdrh::type::PSY;
    }
    else if(pdrh::par_map.empty())
    {
        pdrh::model_type = pdrh::type::NPHA;
        //pdrh::model_type = pdrh::type::PHA;
    }
    else
    {
        pdrh::model_type = pdrh::type::NPHA;
    }
}


//void update_reset(pdrh::mode::jump& j)
//{
//    // variables
//    for(auto it = pdrh::var_map.begin(); it != pdrh::var_map.end(); it++)
//    {
//        if(j.reset.find(it->first) == j.reset.end())
//        {
//            cout << it->first << " not in reset" << endl;
//            j.reset.insert(make_pair(it->first, new pdrh::node(it->first)));
//        }
//    }
//    // nondeterministic parameters
//    for(auto it = pdrh::par_map.begin(); it != pdrh::par_map.end(); it++)
//    {
//        j.reset.insert(make_pair(it->first, new pdrh::node(it->first)));
//    }
//    // discrete random parameters
//    for(auto it = pdrh::dd_map.begin(); it != pdrh::dd_map.end(); it++)
//    {
//        j.reset.insert(make_pair(it->first, new pdrh::node(it->first)));
//    }
//    // continuous random parameters
//    for(auto it = pdrh::rv_map.begin(); it != pdrh::rv_map.end(); it++)
//    {
//        j.reset.insert(make_pair(it->first, new pdrh::node(it->first)));
//    }
//}
//
//void pdrh::update_resets()
//{
//    for(pdrh::mode m : pdrh::modes)
//    {
//        for(pdrh::mode::jump j : m.jumps)
//        {
//            update_reset(j);
//        }
//    }
//}
















