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

