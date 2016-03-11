//
// Created by fedor on 26/12/15.
//
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>

#include "box.h"
box::box()
{

}

// returns true if box is empty
bool box::empty()
{
    return (get_map().size() == 0);
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

bool operator<(const box& lhs, const box& rhs)
{
    // checking if dimensions of the boxes are the same
    if(lhs.get_vars() != rhs.get_vars())
    {
        std::stringstream s;
        s << "Variables of the compared boxes are not the same";
        throw std::invalid_argument(s.str());
    }
    std::map<std::string, capd::interval> lhs_map = lhs.get_map();
    std::map<std::string, capd::interval> rhs_map = rhs.get_map();
    for(auto it = lhs_map.cbegin(); it != lhs_map.cend(); it++)
    {
        if(it->second.leftBound() < rhs_map[it->first].leftBound())
        {
            return true;
        }
    }
    return false;
}

bool operator==(const box& lhs, const box& rhs)
{
    // checking if dimensions of the boxes are the same
    if(lhs.get_vars() != rhs.get_vars())
    {
        std::stringstream s;
        s << "Variables of the compared boxes are not the same";
        throw std::invalid_argument(s.str());
    }
    std::map<std::string, capd::interval> lhs_map = lhs.get_map();
    std::map<std::string, capd::interval> rhs_map = rhs.get_map();
    for(auto it = lhs_map.cbegin(); it != lhs_map.cend(); it++)
    {
        if((it->second.leftBound() != rhs_map[it->first].leftBound()) ||
                (it->second.rightBound() != rhs_map[it->first].rightBound()))
        {
            return false;
        }
    }
    return true;
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

dd_box::dd_box(box b):box(b.get_map())
{

}

rv_box::rv_box(std::map<std::string, capd::interval> e):box(e)
{

}

rv_box::rv_box(box b):box(b.get_map())
{

}

nd_box::nd_box(std::map<std::string, capd::interval> e):box(e)
{

}

nd_box::nd_box(box b):box(b.get_map())
{

}

/**
 * Returns the edges of the box
 */
std::vector<capd::interval> box::get_intervals() const
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
std::vector<std::string> box::get_vars() const
{
    std::vector<std::string> v;
    for(auto it = edges.cbegin(); it != edges.cend(); it++)
    {
        v.push_back(it->first);
    }
    return v;
}