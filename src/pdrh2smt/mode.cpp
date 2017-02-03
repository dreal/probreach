//
// Created by fedor on 03/02/17.
//

#include "mode.h"

mode::mode()
{

}

mode::mode(int id, vector<node> invts, vector<jump> jumps, map<string, node> ode_map)
{
    this->id = id;
    this->invts = invts;
    this->jumps = jumps;
    this->ode_map = ode_map;
}

int mode::get_id()
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

