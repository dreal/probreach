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

box rnd::get_sample(gsl_rng* r)
{
    std::map<std::string, capd::interval> edges;
    // continuous distributions
    for(auto it = pdrh::rv_map.cbegin(); it != pdrh::rv_map.cend(); it++)
    {
        if(pdrh::distribution::uniform.find(it->first) != pdrh::distribution::uniform.cend())
        {
            edges.insert(std::make_pair(it->first,
                                        pdrh::distribution::uniform[it->first].first + gsl_rng_uniform(r) *
                                            (pdrh::distribution::uniform[it->first].second - pdrh::distribution::uniform[it->first].first)));
        }
        else if(pdrh::distribution::normal.find(it->first) != pdrh::distribution::normal.cend())
        {
            edges.insert(std::make_pair(it->first, pdrh::distribution::normal[it->first].first +
                                            gsl_ran_gaussian_ziggurat(r, pdrh::distribution::normal[it->first].second.mid().leftBound())));
        }
        else if(pdrh::distribution::exp.find(it->first) != pdrh::distribution::exp.cend())
        {
            edges.insert(std::make_pair(it->first, gsl_ran_exponential(r, pdrh::distribution::exp[it->first].mid().leftBound())));
        }
        else if(pdrh::distribution::gamma.find(it->first) != pdrh::distribution::gamma.cend())
        {
            edges.insert(std::make_pair(it->first, gsl_ran_gamma(r, pdrh::distribution::gamma[it->first].first.mid().leftBound(),
                                                                 pdrh::distribution::gamma[it->first].second.mid().leftBound())));
        }
        else
        {
            CLOG(ERROR, "ran_gen") << "Random number generator for the variable \"" << it->first << "\" is not supported";
        }
    }
    //discrete distributions
    for(auto it = pdrh::dd_map.cbegin(); it != pdrh::dd_map.cend(); it++)
    {
        std::map<capd::interval, capd::interval> mass_map = pdrh::dd_map[it->first];
        double* p_mass = new double(mass_map.size());
        double* p_value = new double(mass_map.size());
        size_t i = 0;
        // getting values and their probabilities
        for(auto it2 = mass_map.cbegin(); it2 != mass_map.cend(); it2++)
        {
            p_value[i] = it2->first.leftBound();
            p_mass[i] = it2->second.leftBound();
            i++;
        }
        // getting a pointer to the look up table
        gsl_ran_discrete_t* g = gsl_ran_discrete_preproc(mass_map.size(), p_mass);
        // getting a value index
        size_t index = gsl_ran_discrete(r, g);
        edges.insert(std::make_pair(it->first, p_value[index]));
        // releasing memory
        free(p_value);
        free(p_mass);
        gsl_ran_discrete_free(g);
    }

    return box(edges);
}