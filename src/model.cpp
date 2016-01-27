//
// Created by fedor on 24/01/16.
//

#include "model.h"
#include <map>

int pdrh::type;
std::map<std::string, std::tuple<std::string, capd::interval, capd::interval>> pdrh::rv_map;
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
void pdrh::push_invt(pdrh::mode& m, std::string invt)
{
    m.invts.push_back(invt);
}

void pdrh::push_mode(pdrh::mode m)
{
    pdrh::modes.push_back(m);
}

void pdrh::push_ode(pdrh::mode& m, std::string var, std::string ode)
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

void pdrh::push_reset(pdrh::mode& m, pdrh::mode::jump& j, std::string var, std::string expr)
{
    // implement error check
    j.reset.insert(make_pair(var, expr));
}

void pdrh::push_jump(pdrh::mode& m, mode::jump j)
{
    m.jumps.push_back(j);
}

bool pdrh::check_var(std::string var)
{
    return (pdrh::var_map.find(var) != pdrh::var_map.cend());
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

void pdrh::push_rv(std::string var, std::string pdf, capd::interval domain, capd::interval start)
{
    pdrh::rv_map.insert(make_pair(var, make_tuple(pdf, domain, start)));
}

void pdrh::push_dd(std::string var, std::map<capd::interval, capd::interval> m)
{
    pdrh::dd_map.insert(make_pair(var, m));
}

std::string pdrh::print_model()
{
    std::stringstream out;
    out << "VARIABLES:" << std::endl;
    for(auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
    {
        out << "|   " << it->first << " " << it->second << std::endl;
    }
    out << "CONTINUOUS RANDOM VARIABLES:" << std::endl;
    for(auto it = pdrh::rv_map.cbegin(); it != pdrh::rv_map.cend(); it++)
    {
        out << "|   pdf(" << it->first << ") = " << std::get<0>(it->second) << "  | " << std::get<1>(it->second) << " |   " << std::get<2>(it->second) << std::endl;
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
        for(std::string s : m.invts)
        {
            out << "|   |   " << s << std::endl;
        }
        out << "|   FLOW_MAP:" << std::endl;
        for(auto it = m.flow_map.cbegin(); it != m.flow_map.cend(); it++)
        {
            out << "|   |   " << it->first << " " << it->second << std::endl;
        }
        out << "|   ODES:" << std::endl;
        for(auto it = m.odes.cbegin(); it != m.odes.cend(); it++)
        {
            out << "|   |   d[" << it->first << "]/dt = " << it->second << std::endl;
        }
        out << "|   JUMPS:" << std::endl;
        for(pdrh::mode::jump j : m.jumps)
        {
            out << "|   |   GUARD: " << j.guard << std::endl;
            out << "|   |   SUCCESSOR: " << j.next_id << std::endl;
            out << "|   |   RESETS:" << std::endl;
            for(auto it = j.reset.cbegin(); it != j.reset.cend(); it++)
            {
                out << "|   |   |   " << it->first << " := " << it->second << std::endl;
            }
        }
    }
    out << "INIT:" << std::endl;
    for(pdrh::state s : pdrh::init)
    {
        out << "|   MODE: " << s.id << std::endl;
        out << "|   PROPOSITION: " << s.prop << std::endl;
    }
    if(pdrh::goal.size() > 0)
    {
        out << "GOAL:" << std::endl;
        for(pdrh::state s : pdrh::goal)
        {
            out << "|   MODE: " << s.id << std::endl;
            out << "|   PROPOSITION: " << s.prop << std::endl;
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
