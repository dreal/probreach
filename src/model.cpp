//
// Created by fedor on 24/01/16.
//

#include "model.h"
#include <map>
#include <tuple>

int pdrh::type;
std::map<std::string, std::tuple<pdrh::node*, capd::interval, capd::interval>> pdrh::rv_map;
std::map<std::string, std::map<capd::interval, capd::interval>> pdrh::dd_map;
std::map<std::string, capd::interval> pdrh::var_map;
std::map<std::string, capd::interval> pdrh::syn_map;
capd::interval pdrh::time;
std::vector<pdrh::mode> pdrh::modes;
std::vector<pdrh::state> pdrh::init;
std::vector<pdrh::state> pdrh::goal;

// adding a variable
void pdrh::push_var(std::string var, capd::interval domain)
{
    if(capd::intervals::width(domain) < 0)
    {
        std::ostringstream s;
        s << "invalid domain " << domain << " for variable \"" << var << "\"";
        throw std::invalid_argument(s.str());
    }
    if(pdrh::var_map.find(var) != pdrh::var_map.cend())
    {
        std::stringstream s;
        s << "multiple declaration of \"" << var << "\"";
        throw std::invalid_argument(s.str());
    }
    else
    {
        pdrh::var_map.insert(make_pair(var, domain));
    }
}

// adding time bounds
void pdrh::push_time_bounds(capd::interval domain)
{
    if(capd::intervals::width(domain) < 0)
    {
        std::ostringstream s;
        s << "invalid time domain " << domain;
        throw std::invalid_argument(s.str());
    }
    pdrh::time = domain;
}

// adding invariant
void pdrh::push_invt(pdrh::mode& m, pdrh::node* invt)
{
    m.invts.push_back(invt);
}

void pdrh::push_mode(pdrh::mode m)
{
    pdrh::modes.push_back(m);
}

void pdrh::push_ode(pdrh::mode& m, std::string var, pdrh::node* ode)
{
    if(pdrh::var_map.find(var) != pdrh::var_map.cend())
    {
        if(m.flow_map.find(var) == m.flow_map.cend())
        {
            m.flow_map.insert(make_pair(var, pdrh::var_map[var]));
            m.odes.insert(make_pair(var, ode));
        }
        else
        {
            std::stringstream s;
            s << "ode for the variable \"" << var << "\" was already declared above";
            throw std::invalid_argument(s.str());
        }
    }
    else
    {
        std::stringstream s;
        s << "variable \"" << var << "\" appears in the flow but it was not declared";
        throw std::invalid_argument(s.str());
    }
}

void pdrh::push_reset(pdrh::mode& m, pdrh::mode::jump& j, std::string var, pdrh::node* expr)
{
    // implement error check
    j.reset.insert(make_pair(var, expr));
}

void pdrh::push_jump(pdrh::mode& m, mode::jump j)
{
    m.jumps.push_back(j);
}

void pdrh::push_init(std::vector<pdrh::state> s)
{
    pdrh::init = s;
}

void pdrh::push_goal(std::vector<pdrh::state> s)
{
    pdrh::goal = s;
}

void pdrh::push_syn_pair(std::string var, capd::interval e)
{
    pdrh::syn_map.insert(make_pair(var, e));
}

void pdrh::push_rv(std::string var, pdrh::node* pdf, capd::interval domain, capd::interval start)
{
    pdrh::rv_map.insert(make_pair(var, std::make_tuple(pdf, domain, start)));
}

void pdrh::push_dd(std::string var, std::map<capd::interval, capd::interval> m)
{
    pdrh::dd_map.insert(make_pair(var, m));
}

bool pdrh::var_exists(std::string var)
{
    return (pdrh::var_map.find(var) != pdrh::var_map.cend());
}

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

std::vector<pdrh::mode*> pdrh::get_shortest_path(pdrh::mode* begin, pdrh::mode* end)
{
    // initializing the set of paths
    std::vector<std::vector<pdrh::mode*>> paths;
    std::vector<pdrh::mode*> path;
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
            std::vector<pdrh::mode*> successors = pdrh::get_successors(cur_mode);
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
                        if (std::find(path.cbegin(), path.cend(), suc_mode) == path.cend())
                        {
                            std::vector<pdrh::mode*> tmp_path = path;
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

std::vector<std::vector<pdrh::mode*>> pdrh::get_paths(pdrh::mode* begin, pdrh::mode* end, int path_length)
{
    // initializing the set of paths
    std::vector<std::vector<pdrh::mode*>> paths;
    std::vector<pdrh::mode*> path;
    path.push_back(begin);
    // initializing the stack
    std::vector<std::vector<pdrh::mode*>> stack;
    stack.push_back(path);
    while(!stack.empty())
    {
        // getting the first paths from the set of paths
        path = stack.front();
        stack.erase(stack.cbegin());
        // checking if the correct path of the required length is found
        if((path.back() == end) && (path.size() == path_length))
        {
            paths.push_back(path);
        }
        // proceeding only if the length of the current path is smaller then the required length
        else if(path.size() < path_length)
        {
            // getting the last mode in the path
            pdrh::mode* cur_mode = path.back();
            // getting the successors of the mode
            std::vector<pdrh::mode*> successors = pdrh::get_successors(cur_mode);
            for(pdrh::mode* suc_mode : successors)
            {
                // appending the successor the current paths
                std::vector<pdrh::mode*> new_path = path;
                new_path.push_back(suc_mode);
                // pushing the new path to the set of the paths
                stack.push_back(new_path);
            }
        }
    }
    return paths;
}

std::vector<std::vector<pdrh::mode*>> pdrh::get_all_paths(int path_length)
{
    std::vector<std::vector<pdrh::mode*>> res;
    for(pdrh::state i : pdrh::init)
    {
        for(pdrh::state g : pdrh::goal)
        {
            std::vector<std::vector<pdrh::mode*>> paths = pdrh::get_paths(pdrh::get_mode(i.id), pdrh::get_mode(g.id), path_length);
            res.insert(res.end(), paths.begin(), paths.end());
        }
    }
    return res;
}

std::vector<pdrh::mode*> pdrh::get_successors(pdrh::mode* m)
{
    std::vector<pdrh::mode*> res;
    for(pdrh::mode::jump j : m->jumps)
    {
        pdrh::mode *tmp = pdrh::get_mode(j.next_id);
        if(tmp != NULL)
        {
            res.push_back(tmp);
        }
        else
        {
            std::ostringstream s;
            s << "mode \"" << j.next_id << "\" is not defined but appears in the jump: " << pdrh::print_jump(j) << std::endl;
            throw std::invalid_argument(s.str());
        }
    }
    return res;
}

std::vector<pdrh::mode*> pdrh::get_init_modes()
{
    std::vector<pdrh::mode*> res;
    for(pdrh::state st : pdrh::init)
    {
        pdrh::mode *tmp = pdrh::get_mode(st.id);
        if(tmp != NULL)
        {
            res.push_back(tmp);
        }
        else
        {
            std::ostringstream s;
            s << "mode \"" << st.id << "\" is not defined but appears in the init" << std::endl;
            throw std::invalid_argument(s.str());
        }
    }
    return res;
}

std::vector<pdrh::mode*> pdrh::get_goal_modes()
{
    std::vector<pdrh::mode*> res;
    for(pdrh::state st : pdrh::goal)
    {
        pdrh::mode *tmp = pdrh::get_mode(st.id);
        if(tmp != NULL)
        {
            res.push_back(tmp);
        }
        else
        {
            std::ostringstream s;
            s << "mode \"" << st.id << "\" is not defined but appears in the goal" << std::endl;
            throw std::invalid_argument(s.str());
        }
    }
    return res;
}

std::string pdrh::model_to_string()
{
    std::stringstream out;
    out << "MODEL TYPE: " << pdrh::type << std::endl;
    out << "VARIABLES:" << std::endl;
    for(auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
    {
        out << "|   " << it->first << " " << it->second << std::endl;
    }
    out << "CONTINUOUS RANDOM VARIABLES:" << std::endl;
    for(auto it = pdrh::rv_map.cbegin(); it != pdrh::rv_map.cend(); it++)
    {
        out << "|   pdf(" << it->first << ") = " << pdrh::node_to_string_infix(std::get<0>(it->second)) << "  | " << std::get<1>(it->second) << " |   " << std::get<2>(it->second) << std::endl;
    }
    out << "DISCRETE RANDOM VARIABLES:" << std::endl;
    for(auto it = pdrh::dd_map.cbegin(); it != pdrh::dd_map.cend(); it++)
    {
        out << "|   dd(" << it->first << ") = (";
        for(auto it2 = it->second.cbegin(); it2 != it->second.cend(); it2++)
        {
            out << it2->first << " : " << it2->second << ", ";
        }
        out << ")" << std::endl;
    }
    out << "TIME DOMAIN:" << std::endl;
    out << "|   " << pdrh::time << std::endl;
    out << "MODES:" << std::endl;
    for(pdrh::mode m : pdrh::modes)
    {
        out << "|   MODE: " << m.id << ";" << std::endl;
        out << "|   INVARIANTS:" << std::endl;
        for(pdrh::node* n : m.invts)
        {
            out << "|   |   " << pdrh::node_to_string_prefix(n) << std::endl;
        }
        out << "|   FLOW_MAP:" << std::endl;
        for(auto it = m.flow_map.cbegin(); it != m.flow_map.cend(); it++)
        {
            out << "|   |   " << it->first << " " << it->second << std::endl;
        }
        out << "|   ODES:" << std::endl;
        for(auto it = m.odes.cbegin(); it != m.odes.cend(); it++)
        {
            out << "|   |   d[" << it->first << "]/dt = " << pdrh::node_to_string_prefix(it->second) << std::endl;
        }
        out << "|   JUMPS:" << std::endl;
        for(pdrh::mode::jump j : m.jumps)
        {
            out << "|   |   GUARD: " << pdrh::node_to_string_prefix(j.guard) << std::endl;
            out << "|   |   SUCCESSOR: " << j.next_id << std::endl;
            out << "|   |   RESETS:" << std::endl;
            for(auto it = j.reset.cbegin(); it != j.reset.cend(); it++)
            {
                out << "|   |   |   " << it->first << " := " << pdrh::node_to_string_prefix(it->second) << std::endl;
            }
        }
    }
    out << "INIT:" << std::endl;
    for(pdrh::state s : pdrh::init)
    {
        out << "|   MODE: " << s.id << std::endl;
        out << "|   PROPOSITION: " << pdrh::node_to_string_prefix(s.prop) << std::endl;
    }
    if(pdrh::goal.size() > 0)
    {
        out << "GOAL:" << std::endl;
        for(pdrh::state s : pdrh::goal)
        {
            out << "|   MODE: " << s.id << std::endl;
            out << "|   PROPOSITION: " << pdrh::node_to_string_prefix(s.prop) << std::endl;
        }
    }
    else
    {
        out << "SYNTHESIZE:" << std::endl;
        for(auto it = pdrh::syn_map.cbegin(); it != pdrh::syn_map.cend(); it++)
        {
            out << "|   " << it->first << " : " << it->second << std::endl;
        }
    }

    return out.str();
}

std::string pdrh::print_jump(mode::jump j)
{
    std::stringstream out;
    out << j.guard << " ==>  @" << j.next_id << std::endl;
    return out.str();
}

pdrh::node* pdrh::push_terminal_node(std::string value)
{
    pdrh::node* n;
    n = new pdrh::node;
    n->value = value;
    return n;
}

pdrh::node* pdrh::push_operation_node(std::string value, std::vector<pdrh::node*> operands)
{
    pdrh::node* n;
    n = new pdrh::node;
    n->value = value;
    n->operands = operands;
    return n;
}

std::string pdrh::node_to_string_prefix(pdrh::node* n)
{
    std::stringstream s;
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

// implement index modification
/*
std::string pdrh::node_to_string_prefix(pdrh::node* n, int index)
{
    std::stringstream s;
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
*/

bool pdrh::is_var(std::string var)
{
    return pdrh::var_map.find(var) != pdrh::var_map.cend();
}

std::string pdrh::node_to_string_infix(pdrh::node* n)
{
    std::stringstream s;
    // checking whether n is an operation node
    if(n->operands.size() > 0)
    {
        s << "(";
        for(int i = 0; i < n->operands.size() - 1; i++)
        {
            s << pdrh::node_to_string_infix(n->operands.at(i));
            s << n->value;
        }
        s << pdrh::node_to_string_infix(n->operands.at(n->operands.size() - 1));
        s << ")";
    }
    else
    {
        s << n->value;
    }
    return s.str();
}

std::string pdrh::reach_to_smt2(std::vector<pdrh::mode*> path)
{
    std::stringstream s;
    // setting logic
    s << "(set-logic QF_NRA_ODE)" << std::endl;
    // declaring variables and defining bounds
    for(auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
    {
        s << "(declare-fun " << it->first << " () Real)" << std::endl;
        for(int i = 0; i < path.size(); i++)
        {
            s << "(declare-fun " << it->first << "_" << i << "_0 () Real)" << std::endl;
            s << "(assert (>= " << it->first << "_" << i << "_0 " << it->second.leftBound() << ")" << std::endl;
            s << "(assert (<= " << it->first << "_" << i << "_0 " << it->second.rightBound() << ")" << std::endl;
            s << "(declare-fun " << it->first << "_" << i << "_t () Real)" << std::endl;
            s << "(assert (>= " << it->first << "_" << i << "_t " << it->second.leftBound() << ")" << std::endl;
            s << "(assert (<= " << it->first << "_" << i << "_t " << it->second.rightBound() << ")" << std::endl;
        }
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
            s << "))" << std::endl;
        }
    }
    // final statements
    s << "(check-sat)" << std::endl;
    s << "(exit)" << std::endl;
    return s.str();
}
