//
// Created by fedor on 29/12/15.
//

#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include "box.h"
#include "box_factory.h"

/**
 * Cartesian product
 */
std::vector<box> box_factory::cartesian_product(std::map<std::string, std::vector<capd::interval>> m)
{
    unsigned long size = 1;
    for(auto it = m.cbegin(); it != m.cend(); it++)
    {
        size *= (it->second).size();
    }

    std::vector<box> product;
    for(unsigned long i = 0; i < size; i++)
    {
        unsigned long index = i;
        std::map<std::string, capd::interval> tmp_m;
        for(auto it1 = m.cbegin(); it1 != m.cend(); it1++)
        {
            unsigned long mult = 1;
            for(auto it2 = --m.cend(); it2 != it1; it2--)
            {
                mult *= (it2->second).size();
            }
            unsigned long tmp_index = index / mult;
            tmp_m.insert(make_pair(it1->first, (it1->second).at(tmp_index)));
            index -= tmp_index * mult;
        }
        product.push_back(box(tmp_m));
    }
    return product;
}

/**
 * Dividing the box in all n dimensions producing 2^n boxes of the same size
 */
std::vector<box> box_factory::bisect(box b)
{
    std::map<std::string, capd::interval> e;
    std::map<std::string, capd::interval> m = b.get_map();
    for(auto it = m.cbegin(); it != m.cend(); it++)
    {
        e.insert(make_pair(it->first, capd::interval(0)));
    }

    return box_factory::bisect(b,e);
}

/**
 * Dividing the box in all n dimensions producing 2^n boxes of the same size
 * according to the precision vector e
 */
std::vector<box> box_factory::bisect(box b, std::map<std::string, capd::interval> e)
{
    std::map<std::string, std::vector<capd::interval>> tmp_m;
    std::map<std::string, capd::interval> m = b.get_map();
    for(auto it = m.cbegin(); it != m.cend(); it++)
    {
        if(capd::intervals::width(it->second) > e[it->first].leftBound())
        {
            std::vector<capd::interval> tmp_v;
            tmp_v.push_back(capd::interval((it->second).leftBound(), (it->second).mid().rightBound()));
            tmp_v.push_back(capd::interval((it->second).mid().leftBound(), (it->second).rightBound()));
            tmp_m.insert(make_pair(it->first, tmp_v));
        }
    }
    return box_factory::cartesian_product(tmp_m);
}

