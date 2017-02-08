//
// Created by fedor on 02/02/17.
//

#include "node.h"
#include <sstream>
#include <cstring>

node::node()
{

}

node::node(string value)
{
    this->value = value;
}

node::node(string value, vector<node> operands)
{
    this->value = value;
    this->operands = operands;
}

void node::append(node n)
{
    this->operands.push_back(n);
}

void node::append(vector<node> n)
{
    this->operands.insert(this->operands.begin(), n.begin(), n.end());
}

bool node::is_terminal()
{
    return this->operands.empty();
}

bool node::is_number()
{
    return isdigit(this->value.front());
}

bool node::is_empty()
{
    return this->operands.empty() && this->value.empty();
}

string node::to_infix()
{
    return to_infix("");
}

string node::to_infix(string index)
{
    stringstream s;
    // checking whether n is an operation node
    if(this->operands.size() > 1)
    {
        s << "(";
        for(unsigned long i = 0; i < this->operands.size() - 1; i++)
        {
            s << this->operands.at(i).to_infix(index);
            s << this->value;
            // checking if current node is a number
            if(!is_number() && is_terminal())
            {
                s << index;
            }
        }
        s << this->operands.at(this->operands.size() - 1).to_infix(index) << ")";
    }
    else if(this->operands.size() == 1)
    {
        if(strcmp(this->value.c_str(), "-") == 0)
        {
            s << "(" << this->value;
            // checking if current node is a number
            if(!is_number() && is_terminal())
            {
                s << index;
            }
            s << this->operands.front().to_infix(index) << ")";
        }
        else
        {
            s << this->value;
            if(!is_number() && is_terminal())
            {
                s << index;
            }
            s << "(" << this->operands.front().to_infix(index) << ")";
        }
    }
    else
    {
        s << this->value;
        if(!is_number() && is_terminal())
        {
            s << index;
        }
    }
    return s.str();
}

string node::to_prefix()
{
    return to_prefix("");
}

string node::to_prefix(string index)
{
    stringstream s;
    // checking whether n is an operation node
    if(!this->is_terminal())
    {
        s << "(" << this->value;
        if(!is_number() && is_terminal())
        {
            s << index;
        }
        for(node n : this->operands)
        {
            s << n.to_prefix(index);
        }
        s << ")";
    }
    else
    {
        s  << " " << this->value;
        if(!is_number() && is_terminal())
        {
            s << index;
        }
    }
    return s.str();
}

string node::get_value()
{
    return this->value;
}

vector<node> node::get_operands()
{
    return this->operands;
}