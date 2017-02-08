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

vector<node> mode::get_invariants()
{
    return this->invts;
}

vector<jump> mode::get_jumps()
{
    return this->jumps;
}

map<string, node> mode::get_odes()
{
    return this->ode_map;
}

map<string, pair<node, node>> mode::get_vars()
{
    return this->var_map;
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
