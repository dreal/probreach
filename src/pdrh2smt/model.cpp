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
    this->init_map.insert(make_pair(id, pred));
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
    this->goal_map.insert(make_pair(id, pred));
}

bool model::var_exists(string var)
{
    return (this->var_map.find(var) != this->var_map.end());
}