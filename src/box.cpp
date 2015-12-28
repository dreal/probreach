//
// Created by fedor on 26/12/15.
//
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>

#include "box.h"
box::box()
{

}

box::box(std::map<std::string, capd::interval> e)
{
    for(auto it = e.cbegin(); it != e.cend(); it++)
    {
        if(capd::intervals::width(it->second) < 0)
        {
            std::ostringstream s;
            s << "invalid interval " << it->first << ":" << it->second << " while creating a box";
            throw std::invalid_argument(s.str());
        }
    }
    this->edges = e;
}

std::map<std::string, capd::interval> box::get_map() const
{
    return this->edges;
}

std::ostream& operator<<(std::ostream& os, const box& b)
{
    std::map<std::string, capd::interval> e = b.get_map();
    for(auto it = e.cbegin(); it != e.cend(); it++)
    {
        os << it->first << ":" << it->second << "; ";
    }
    return os;
}

dd_box::dd_box(std::map<std::string, capd::interval> e)
{
    for(auto it = e.cbegin(); it != e.cend(); it++)
    {
        if(capd::intervals::width(it->second) > 0)
        {
            std::ostringstream s;
            s << "invalid interval " << it->first << ":" << it->second << " while creating a dd_box";
            throw std::invalid_argument(s.str());
        }
    }
    this->edges = e;
}

rv_box::rv_box(std::map<std::string, capd::interval> e):box(e)
{

}

nd_box::nd_box(std::map<std::string, capd::interval> e):box(e)
{

}

/**
 * Returns the edges of the box
 */
std::vector<capd::interval> box::get_intervals()
{
    std::vector<capd::interval> i;
    for(auto it = edges.cbegin(); it != edges.cend(); it++)
    {
        i.push_back(it->second);
    }
    return i;
}

/**
 * Returns the variables of the box
 */
std::vector<std::string> box::get_vars()
{
    std::vector<std::string> v;
    for(auto it = edges.cbegin(); it != edges.cend(); it++)
    {
        v.push_back(it->first);
    }
    return v;
}