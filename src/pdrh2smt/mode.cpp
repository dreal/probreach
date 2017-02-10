//
// Created by fedor on 03/02/17.
//

#include "mode.h"

mode::mode()
{

}

mode::mode(int id, vector<node> invts, map<string, node> ode_map, vector<jump> jumps)
{
    this->id = id;
    this->invts = invts;
    this->ode_map = ode_map;
    this->jumps = jumps;
}

mode::mode(int id, map<string, node> ode_map, vector<jump> jumps)
{
    this->id = id;
    this->ode_map = ode_map;
    this->jumps = jumps;
}

int mode::get_id() const
{
    return this->id;
}

node mode::get_ode(string var) const
{
    map<string, node> odes = this->ode_map;
    if(odes.find(var) != odes.end())
    {
        return odes[var];
    }
    return node();
}

vector<node> mode::get_invariants()
{
    return this->invts;
}

vector<jump> mode::get_jumps()
{
    return this->jumps;
}

vector<jump> mode::get_jumps(int next_mode)
{
    vector<jump> res;
    for(jump j : this->jumps)
    {
        if(j.get_id() == next_mode)
        {
            res.push_back(j);
        }
    }
    return res;
}

map<string, node> mode::get_odes()
{
    return this->ode_map;
}

vector<string> mode::get_vars()
{
    vector<string> vars;
    for(auto it = this->ode_map.begin(); it != this->ode_map.end(); it++)
    {
        vars.push_back(it->first);
    }
    return vars;
}

vector<int> mode::get_successors()
{
    vector<int> s;
    for(jump j : jumps)
    {
        s.push_back(j.get_id());
    }
    return s;
}

bool operator==(const mode& lhs, const mode& rhs)
{
    return (lhs.get_id() == rhs.get_id());
}

node mode::get_invariants_conjunction()
{
    return node("and", this->invts);
}


