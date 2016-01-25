//
// Created by fedor on 24/01/16.
//

#include "model.h"
#include <map>

int pdrh::type;
std::map<std::string, std::string> pdrh::rv_map;
std::map<std::string, std::map<capd::interval, capd::interval>> pdrh::dd_map;
std::map<std::string, capd::interval> pdrh::var_map;
std::map<std::string, double> pdrh::syn_map;
capd::interval pdrh::time;

void pdrh::push_var(std::string var, capd::interval domain)
{
    if(capd::intervals::width(domain) < 0)
    {
        std::ostringstream s;
        s << "invalid domain " << domain << " for variable \"" << var << "\"";
        throw std::invalid_argument(s.str());
    }
    if(pdrh::var_map.find(var) != pdrh::var_map.cend())
    {
        std::stringstream s;
        s << "multiple definition of \"" << var << "\"";
        throw std::invalid_argument(s.str());
    }
    else
    {
        pdrh::var_map.insert(make_pair(var, domain));
    }
}

void pdrh::push_time_bounds(capd::interval domain)
{
    if(capd::intervals::width(domain) < 0)
    {
        std::ostringstream s;
        s << "invalid time domain " << domain;
        throw std::invalid_argument(s.str());
    }
    pdrh::time = domain;
}