//
// Created by fedor on 26/12/15.
//
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>

#include "box.h"
#include "box_factory.h"

using namespace std;

box::box()
{

}

// returns true if box is empty
bool box::empty()
{
    return (get_map().size() == 0);
}

bool box::contains(box b)
{
    map<string, capd::interval> edges = get_map();
    map<string, capd::interval> b_edges = b.get_map();
    for(auto it = edges.cbegin(); it != edges.cend(); it++)
    {
        if(b_edges.find(it->first) != b_edges.cend())
        {
            if(!it->second.contains(b.get_map()[it->first]))
            {
                return false;
            }
        }
        else
        {
            ostringstream s;
            s << "The target box does not contain varibale: \"" << it->first << "\"";
            throw invalid_argument(s.str());
        }
    }
    return true;
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

box operator+(const box& lhs, const box& rhs)
{
    if(!box_factory::get_keys_diff(lhs, rhs).empty() ||
            !box_factory::get_keys_diff(rhs, lhs).empty())
    {
        ostringstream s;
        s << "cannot perform \"+\" operation for " << lhs << " and " << rhs << ". The boxes have different sets of variables";
        throw std::invalid_argument(s.str());
    }
    map<string, capd::interval> lhs_map = lhs.get_map();
    map<string, capd::interval> rhs_map = rhs.get_map();
    map<string, capd::interval> res;
    for(auto it = lhs_map.cbegin(); it != lhs_map.cend(); it++)
    {
        res.insert(make_pair(it->first, it->second + rhs_map[it->first]));
    }
    return box(res);
}

box operator-(const box& lhs, const box& rhs)
{
    if(!box_factory::get_keys_diff(lhs, rhs).empty() ||
            !box_factory::get_keys_diff(rhs, lhs).empty())
    {
        ostringstream s;
        s << "cannot perform \"+\" operation for " << lhs << " and " << rhs << ". The boxes have different sets of variables";
        throw std::invalid_argument(s.str());
    }
    map<string, capd::interval> lhs_map = lhs.get_map();
    map<string, capd::interval> rhs_map = rhs.get_map();
    map<string, capd::interval> res;
    for(auto it = lhs_map.cbegin(); it != lhs_map.cend(); it++)
    {
        res.insert(make_pair(it->first, it->second - rhs_map[it->first]));
    }
    return box(res);
}

box operator*(const box& lhs, const box& rhs)
{
    if(!box_factory::get_keys_diff(lhs, rhs).empty() ||
            !box_factory::get_keys_diff(rhs, lhs).empty())
    {
        ostringstream s;
        s << "cannot perform \"+\" operation for " << lhs << " and " << rhs << ". The boxes have different sets of variables";
        throw std::invalid_argument(s.str());
    }
    map<string, capd::interval> lhs_map = lhs.get_map();
    map<string, capd::interval> rhs_map = rhs.get_map();
    map<string, capd::interval> res;
    for(auto it = lhs_map.cbegin(); it != lhs_map.cend(); it++)
    {
        res.insert(make_pair(it->first, it->second * rhs_map[it->first]));
    }
    return box(res);
}

box operator/(const box& lhs, const box& rhs)
{
    if(!box_factory::get_keys_diff(lhs, rhs).empty() ||
            !box_factory::get_keys_diff(rhs, lhs).empty())
    {
        ostringstream s;
        s << "cannot perform \"+\" operation for " << lhs << " and " << rhs << ". The boxes have different sets of variables";
        throw std::invalid_argument(s.str());
    }
    map<string, capd::interval> lhs_map = lhs.get_map();
    map<string, capd::interval> rhs_map = rhs.get_map();
    map<string, capd::interval> res;
    for(auto it = lhs_map.cbegin(); it != lhs_map.cend(); it++)
    {
        res.insert(make_pair(it->first, it->second / rhs_map[it->first]));
    }
    return box(res);
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

box box::get_mean()
{
    map<string, capd::interval> edges = get_map();
    map<string, capd::interval> mu_map;
    for(auto it = edges.cbegin(); it != edges.cend(); it++)
    {
        mu_map.insert(make_pair(it->first, it->second.mid()));
    }
    return box(mu_map);
}

box box::get_stddev()
{
    map<string, capd::interval> edges = get_map();
    map<string, capd::interval> sigma_map;
    for(auto it = edges.cbegin(); it != edges.cend(); it++)
    {
        sigma_map.insert(make_pair(it->first, capd::intervals::width(
                capd::interval(it->second.leftBound(),
                               it->second.mid().leftBound()))));
    }
    return box(sigma_map);
}

double box::max()
{
    map<string, capd::interval> edges = get_map();
    double max = edges.cbegin()->second.leftBound();
    for(auto it = edges.cbegin(); it != edges.cend(); it++)
    {
        if(it->second.leftBound() > max)
        {
            max = it->second.leftBound();
        }
    }
    return max;
}