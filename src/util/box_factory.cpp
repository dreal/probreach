//
// Created by fedor on 29/12/15.
//

#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include "box.h"
#include "box_factory.h"
#include "pdrh_config.h"

/**
 * Cartesian product
 */
std::vector<box> box_factory::cartesian_product(std::map<std::string, std::vector<capd::interval>> m)
{
    // checking if the map is empty
    if(m.empty())
    {
        return vector<box>{};
    }

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

// partitioning a box
vector<box> box_factory::partition(box b, double e)
{
    // setting up a precision map
    map<string, capd::interval> e_map;
    map<string, capd::interval> edges = b.get_map();
    for(auto it = edges.cbegin(); it != edges.cend(); it++)
    {
        e_map.insert(make_pair(it->first, capd::interval(e)));
    }
    // main algorithm
    vector<box> q = {b};
    vector<box> res;
    while(!q.empty())
    {
        box tmp_b = q.front();
        q.erase(q.cbegin());
        vector<box> tmp_v = bisect(tmp_b, e_map);
        if(tmp_v.empty())
        {
            res.push_back(tmp_b);
        }
        else
        {
            q.insert(q.cend(), tmp_v.cbegin(), tmp_v.cend());
        }
    }
    return res;
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

/**
 * Dividing the box in all n dimensions producing 2^n boxes of the same size
 * according to the precision vector e
 */
vector<box> box_factory::bisect(box b, map<string, pdrh::node*> e)
{
    std::map<std::string, std::vector<capd::interval>> tmp_m;
    std::map<std::string, capd::interval> m = b.get_map();
    for(auto it = m.cbegin(); it != m.cend(); it++)
    {
        if(capd::intervals::width(it->second) > pdrh::node_to_interval(e[it->first]).leftBound())
        {
            std::vector<capd::interval> tmp_v;
            tmp_v.push_back(capd::interval((it->second).leftBound(), (it->second).mid().rightBound()));
            tmp_v.push_back(capd::interval((it->second).mid().leftBound(), (it->second).rightBound()));
            tmp_m.insert(make_pair(it->first, tmp_v));
        }
    }
    return box_factory::cartesian_product(tmp_m);
}

std::vector<box> box_factory::merge(std::vector<box> boxes)
{
    unsigned long i = 0;
    while(i < boxes.size())
    {
        unsigned long previous_size = boxes.size();
        for(unsigned long j = i + 1; j < boxes.size(); j++)
        {
            box b = merge(boxes.at(i), boxes.at(j));
            if(!b.empty())
            {
                boxes.at(i) = b;
                boxes.erase(boxes.begin() + j);
                i = 0;
                break;
            }
        }
        if(boxes.size() == previous_size)
        {
            i++;
        }
    }
    return boxes;
}

box box_factory::merge(box lhs, box rhs)
{
    std::map<std::string, capd::interval> m = lhs.get_map();
    for(auto it = m.cbegin(); it != m.cend(); it++)
    {
        if(rhs.get_map().find(it->first) == rhs.get_map().cend())
        {
            std::stringstream s;
            s << "Variables of the compared boxes are not the same";
            throw std::invalid_argument(s.str());
        }
    }
    int neq_counter = 0;
    std::string neq_dim;

    for(auto it = m.cbegin(); it != m.cend(); it++)
    {
        //std::cout << it->first << " " << it->second << std::endl;
        if(it->second != rhs.get_map()[it->first])
        {
            neq_counter++;
            neq_dim = it->first;
        }

        if(neq_counter > 1)
        {
            return box();
        }
    }

    if(m[neq_dim].rightBound() == rhs.get_map()[neq_dim].leftBound())
    {
        m[neq_dim] = capd::interval(m[neq_dim].leftBound(), rhs.get_map()[neq_dim].rightBound());
        return box(m);
    }
    else
    {
        if(m[neq_dim].leftBound() == rhs.get_map()[neq_dim].rightBound())
        {
            m[neq_dim] = capd::interval(rhs.get_map()[neq_dim].leftBound(), m[neq_dim].rightBound());
            return box(m);
        }
        else
        {
            return box();
        }
    }
}

box box_factory::get_mean(vector<box> q)
{
    box f_box = q.front();
    map<string, capd::interval> f_map = f_box.get_map();
    // setting the initial box
    map<string, capd::interval> init_map, div_map;
    for(auto it = f_map.cbegin(); it != f_map.cend(); it++)
    {
        init_map.insert(make_pair(it->first, capd::interval(0.0)));
        div_map.insert(make_pair(it->first, capd::interval(q.size())));
    }
    box res(init_map), div(div_map);
    for(box b : q)
    {
        res = res + b.get_mean();
    }
    return res / div;
}

box box_factory::get_stddev(vector<box> q)
{
    box mean = get_mean(q);
    map<string, capd::interval> f_map = mean.get_map();
    // setting the initial box
    map<string, capd::interval> init_map, div_map;
    for(auto it = f_map.cbegin(); it != f_map.cend(); it++)
    {
        init_map.insert(make_pair(it->first, capd::interval(0.0)));
        div_map.insert(make_pair(it->first, capd::interval(q.size())));
    }
    box sum(init_map), div(div_map);
    for(box b : q)
    {
        sum = sum + (b.get_mean() - mean) * (b.get_mean() - mean);
    }
    return box_factory::sqrt(sum/div);
}

box box_factory::sqrt(box b)
{
    map<string, capd::interval> b_map = b.get_map();
    map<string, capd::interval> res;
    for(auto it = b_map.cbegin(); it != b_map.cend(); it++)
    {
        res.insert(make_pair(it->first, capd::intervals::sqrt(it->second)));
    }
    return box(res);
}

box box_factory::get_keys_diff(box lhs, box rhs)
{
    map<string, capd::interval> res;
    map<string, capd::interval> lhs_map = lhs.get_map();
    map<string, capd::interval> rhs_map = rhs.get_map();
    for(auto it = lhs_map.cbegin(); it != lhs_map.cend(); it++)
    {
        if(rhs_map.find(it->first) == rhs_map.cend())
        {
            res.insert(make_pair(it->first, it->second));
        }
    }
    return box(res);
}

/*
vector<pair<box, capd::interval>> box_factory::sort(vector<pair<box, capd::interval>> q)
{
    for(int i = 1; i < q.size(); i++)
    {
        for(int j = 0; j < q.size() - 1; j++)
        {
            if(q.at(j).second.mid().leftBound() > q.at(j+1).second.mid().leftBound())
            {
                pair<box, capd::interval> tmp = q.at(j+1);
                q.at(j+1) = q.at(j);
                q.at(j) = tmp;
            }
        }
    }
    return q;
}
*/

box box_factory::get_cover(vector<box> q)
{
    sort(q.begin(), q.end());
    if(!box_factory::get_keys_diff(q.front(), q.back()).empty() ||
       !box_factory::get_keys_diff(q.back(), q.front()).empty())
    {
        ostringstream s;
        s << "could not get_cover for " << q.front() << " and " << q.back() << ". The boxes have different sets of variables";
        throw std::invalid_argument(s.str());
    }
    map<string, capd::interval> min = q.front().get_map();
    map<string, capd::interval> max = q.back().get_map();
    map<string, capd::interval> res;
    for(auto it = min.begin(); it != min.end(); it++)
    {
        res.insert(make_pair(it->first, capd::interval(it->second.leftBound(), max[it->first].rightBound())));
    }
    return box(res);
}
