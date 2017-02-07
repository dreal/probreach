//
// Created by fedor on 03/02/17.
//

#include <sstream>
#include "model.h"

model::model()
{

}

void model::set_time(node lhs, node rhs)
{
    if(!this->time.first.is_empty() || !this->time.second.is_empty())
    {
        throw invalid_argument("time variable should be defined only once");
    }
    this->time = make_pair(lhs, rhs);
}

void model::push_var(string var, node lhs, node rhs)
{
    if(this->var_map.find(var) != this->var_map.end())
    {
        stringstream s;
        s << "variable " << var << " has already been declared";
        throw invalid_argument(s.str());
    }
    this->var_map.insert(make_pair(var, make_pair(lhs, rhs)));
}

void model::push_mode(mode md)
{
    for(mode m : this->modes)
    {
        if(m.get_id() == md.get_id())
        {
            stringstream s;
            s << "mode with id " << md.get_id() << " has already been created";
            throw invalid_argument(s.str());
        }
    }
    this->modes.push_back(md);
}

void model::push_init(int id, node pred)
{
    bool mode_exists = false;
    for(mode m : this->modes)
    {
        if(m.get_id() == id)
        {
            mode_exists = true;
        }
    }
    if(!mode_exists)
    {
        stringstream s;
        s << "mode with id " << id << " is not in the model";
    }
    this->inits.push_back(make_pair(id, pred));
}

void model::push_goal(int id, node pred)
{
    bool mode_exists = false;
    for(mode m : this->modes)
    {
        if(m.get_id() == id)
        {
            mode_exists = true;
        }
    }
    if(!mode_exists)
    {
        stringstream s;
        s << "mode with id " << id << " is not in the model";
    }
    this->goals.push_back(make_pair(id, pred));
}

bool model::var_exists(string var)
{
    return (this->var_map.find(var) != this->var_map.end());
}


std::ostream& operator<<(std::ostream& os, model& m)
{
    os << "VARIABLES:" << endl;
    map<string, pair<node, node>> vars = m.get_var_map();
    for(auto it = vars.begin(); it != vars.end(); it++)
    {
        os << "|   " << it->first << " [" << it->second.first.to_string_infix() << ", " <<
        it->second.second.to_string_infix() << "]" << endl;
    }
    /*
    os << "CONTINUOUS RANDOM VARIABLES:" << endl;
    for(auto it = pdrh::rv_map.cbegin(); it != pdrh::rv_map.cend(); it++)
    {
        os << "|   pdf(" << it->first << ") = " << pdrh::node_to_string_infix(get<0>(it->second)) << "  | "
        << pdrh::node_to_string_prefix(get<1>(it->second)) << " |   "
        << pdrh::node_to_string_prefix(get<2>(it->second)) << "    |   "
        << pdrh::node_to_string_prefix(get<3>(it->second)) << endl;
    }
    os << "DISCRETE RANDOM VARIABLES:" << endl;
    for(auto it = pdrh::dd_map.cbegin(); it != pdrh::dd_map.cend(); it++)
    {
        os << "|   dd(" << it->first << ") = (";
        for(auto it2 = it->second.cbegin(); it2 != it->second.cend(); it2++)
        {
            cout << pdrh::node_to_string_prefix(it2->first) << " : " << pdrh::node_to_string_prefix(it2->second) << endl;
            os << pdrh::node_to_string_prefix(it2->first) << " : " << pdrh::node_to_string_prefix(it2->second) << ", ";
        }
        os << ")" << endl;
    }
    */
    os << "TIME DOMAIN:" << endl;
    os << "|   [" << m.get_time_bounds().first.to_string_infix() << ", " << m.get_time_bounds().second.to_string_infix() << "]" << endl;
    os << "MODES:" << endl;
    for(mode md : m.get_modes())
    {
        os << "|   MODE: " << md.get_id() << ";" << endl;
        os << "|   INVARIANTS:" << endl;
        for(node n : md.get_invariants())
        {
            os << "|   |   " << n.to_string_infix() << endl;
        }
        os << "|   FLOW_MAP:" << endl;
        map<string, pair<node, node>> flow_map = md.get_vars();
        for(auto it = flow_map.begin(); it != flow_map.end(); it++)
        {
            os << "|   " << it->first << " " << " [" << it->second.first.to_string_infix() << ", " <<
            it->second.second.to_string_infix() << "]" << endl;
        }
        os << "|   ODES:" << endl;
        map<string, node> ode_map = md.get_odes();
        for(auto it = ode_map.begin(); it != ode_map.end(); it++)
        {
            os << "|   |   d[" << it->first << "]/dt = " << it->second.to_string_infix() << endl;
        }
        os << "|   JUMPS:" << endl;
        for(jump j : md.get_jumps())
        {
            os << "|   |   GUARD: " << j.get_guard().to_string_infix() << endl;
            os << "|   |   SUCCESSOR: " << j.get_id() << endl;
            os << "|   |   RESETS:" << endl;
            map<string, node> reset_map = j.get_reset_map();
            for(auto it = reset_map.begin(); it != reset_map.end(); it++)
            {
                os << "|   |   |   " << it->first << " := " << it->second.to_string_infix() << endl;
            }
        }
    }
    os << "INIT:" << endl;
    for(pair<int, node> s : m.get_inits())
    {
        os << "|   MODE: " << s.first << endl;
        os << "|   PROPOSITION: " << s.second.to_string_infix() << endl;
    }
    if(m.get_goals().size() > 0)
    {
        os << "GOAL:" << endl;
        for(pair<int, node> s : m.get_goals())
        {
            os << "|   MODE: " << s.first << endl;
            os << "|   PROPOSITION: " << s.second.to_string_infix() << endl;
        }
    }
    else
    {
        /*
        os << "SYNTHESIZE:" << endl;
        for(auto it = pdrh::syn_map.cbegin(); it != pdrh::syn_map.cend(); it++)
        {
            os << "|   " << it->first << " " << pdrh::node_to_string_prefix(it->second) << endl;
        }
        */
    }
    return os;
}



// getters and setters
map<string, pair<node, node>> model::get_var_map()
{
    return this->var_map;
}

pair<node, node> model::get_time_bounds()
{
    return this->time;
}

vector<mode> model::get_modes()
{
    return this->modes;
}

vector<pair<int, node>> model::get_inits()
{
    return this->inits;
}

vector<pair<int, node>> model::get_goals()
{
    return this->goals;
}