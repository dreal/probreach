//
// Created by fedor on 03/02/17.
//

#include <sstream>
#include "jump.h"

jump::jump()
{

}

jump::jump(int id, node guard)
{
    this->id = id;
    this->guard = guard;
}

jump::jump(int id, node guard, map<string, node> reset_map)
{
    this->id = id;
    this->guard = guard;
    this->reset_map = reset_map;
}

int jump::get_id()
{
    return this->id;
}

node jump::get_guard()
{
    return this->guard;
}

map<string, node> jump::get_reset_map()
{
    return this->reset_map;
}

void jump::push_reset(string var, node reset)
{
    if(this->reset_map.find(var) != this->reset_map.end())
    {
        stringstream s;
        s << "reset value for variable " << var << " has already been defined";
        throw invalid_argument(s.str());
    }
    this->reset_map.insert(make_pair(var, reset));
}