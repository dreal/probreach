//
// Created by fedor on 04/04/16.
//

#include "rnd.h"
#include "model.h"
#include <gsl/gsl_rng.h>
#include <gsl/gsl_randist.h>
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include <logging/easylogging++.h>

using namespace std;

box rnd::get_random_sample(gsl_rng* r)
{
    map<std::string, capd::interval> edges;
    // continuous distributions
    for(auto it = pdrh::rv_map.cbegin(); it != pdrh::rv_map.cend(); it++)
    {
        if(pdrh::distribution::uniform.find(it->first) != pdrh::distribution::uniform.cend())
        {
            edges.insert(make_pair(it->first,
                                        pdrh::node_to_interval(pdrh::distribution::uniform[it->first].first) + gsl_rng_uniform(r) *
                                            (pdrh::node_to_interval(pdrh::distribution::uniform[it->first].second) -
                                                    pdrh::node_to_interval(pdrh::distribution::uniform[it->first].first))));
        }
        else if(pdrh::distribution::normal.find(it->first) != pdrh::distribution::normal.cend())
        {
            edges.insert(make_pair(it->first, pdrh::node_to_interval(pdrh::distribution::normal[it->first].first) +
                                            gsl_ran_gaussian_ziggurat(r, pdrh::node_to_interval(pdrh::distribution::normal[it->first].second).mid().leftBound())));
        }
        else if(pdrh::distribution::exp.find(it->first) != pdrh::distribution::exp.cend())
        {
            edges.insert(make_pair(it->first, gsl_ran_exponential(r, pdrh::node_to_interval(pdrh::distribution::exp[it->first]).mid().leftBound())));
        }
        else if(pdrh::distribution::gamma.find(it->first) != pdrh::distribution::gamma.cend())
        {
            edges.insert(make_pair(it->first, gsl_ran_gamma(r, pdrh::node_to_interval(pdrh::distribution::gamma[it->first].first).mid().leftBound(),
                                                                 pdrh::node_to_interval(pdrh::distribution::gamma[it->first].second).mid().leftBound())));
        }
        else
        {
            CLOG(ERROR, "ran_gen") << "Random number generator for the variable \"" << it->first << "\" is not supported";
        }
    }
    //discrete distributions
    for(auto it = pdrh::dd_map.cbegin(); it != pdrh::dd_map.cend(); it++)
    {
        map<pdrh::node*, pdrh::node*> mass_map = pdrh::dd_map[it->first];
        double* p_mass = new double[mass_map.size()];
        pdrh::node** p_value = new pdrh::node*[mass_map.size()];
        size_t i = 0;
        // getting values and their probabilities
        for(auto it2 = mass_map.cbegin(); it2 != mass_map.cend(); it2++)
        {
            p_value[i] = it2->first;
            p_mass[i] = pdrh::node_to_interval(it2->second).mid().leftBound();
            i++;
        }
        // getting a pointer to the look up table
        gsl_ran_discrete_t* g = gsl_ran_discrete_preproc(mass_map.size(), p_mass);
        // getting a value index
        size_t index = gsl_ran_discrete(r, g);
        edges.insert(std::make_pair(it->first, pdrh::node_to_interval(p_value[index])));
        // releasing memory
        delete p_value;
        delete p_mass;
        gsl_ran_discrete_free(g);
    }
    return box(edges);
}

box rnd::get_sobol_sample(gsl_qrng* q, box b)
{
    // drawing a sample
    double v[b.get_map().size()];
    gsl_qrng_get (q, v);

    map<std::string, capd::interval> edges, b_edges;
    b_edges = b.get_map();
    int i = 0;
    // continuous distributions
    for(auto it = b_edges.cbegin(); it != b_edges.cend(); it++)
    {
        edges.insert(make_pair(it->first, capd::interval(it->second.leftBound() + v[i] * capd::intervals::width(it->second))));
        i++;
    }
    return box(edges);
}

box rnd::get_normal_random_sample(gsl_rng* r, box mu, box sigma)
{
    map<std::string, capd::interval> edges;
    for(auto it = pdrh::par_map.cbegin(); it != pdrh::par_map.cend(); it++)
    {
        if(find(mu.get_vars().cbegin(), mu.get_vars().cend(), it->first) != mu.get_vars().cend() &&
                find(sigma.get_vars().cbegin(), sigma.get_vars().cend(), it->first) != sigma.get_vars().cend())
        {
            edges.insert(make_pair(it->first, mu.get_map()[it->first].mid().leftBound() +
                                              gsl_ran_gaussian_ziggurat(r, sigma.get_map()[it->first].mid().leftBound())));
        }
        else
        {
            CLOG(ERROR, "ran_gen") << "Parameter \"" << it->first << "\" is not defined";
        }
    }
    return box(edges);
}