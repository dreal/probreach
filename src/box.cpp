//
// Created by fedor on 26/12/15.
//

#include "box.h"

box::box(std::map<std::string, capd::interval> edges)
{
    // !!! check if all the variables are defined and all the intervals are correct
    this->edges = edges;
}

std::map<std::string, capd::interval> box::get_edges() const
{
    return this->edges;
}

std::ostream& operator<<(std::ostream& strm, const box& b)
{
    for(auto it = b.get_edges().begin(); it != b.get_edges().end(); it++)
    {
        strm << it->first << ":" << it->second << ";";
    }
    return strm;
}