//
// Created by fedor on 04/04/16.
//

#include "rnd.h"
#include "model.h"
#include "box_factory.h"
#include "pdrh2box.h"
#include <gsl/gsl_rng.h>
#include <gsl/gsl_randist.h>
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include <logging/easylogging++.h>
#include <gsl/gsl_vector_double.h>
#include <gsl/gsl_multiroots.h>
#include <gsl/gsl_cdf.h>

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
                                   pdrh2box::node_to_interval(pdrh::distribution::uniform[it->first].first) + gsl_rng_uniform(r) *
                                            (pdrh2box::node_to_interval(
                                                    pdrh::distribution::uniform[it->first].second) -
                                                    pdrh2box::node_to_interval(
                                                            pdrh::distribution::uniform[it->first].first))));
        }
        else if(pdrh::distribution::normal.find(it->first) != pdrh::distribution::normal.cend())
        {
            edges.insert(make_pair(it->first,
                                   pdrh2box::node_to_interval(pdrh::distribution::normal[it->first].first) +
                                            gsl_ran_gaussian_ziggurat(r, pdrh2box::node_to_interval(
                                                    pdrh::distribution::normal[it->first].second).mid().leftBound())));
        }
        else if(pdrh::distribution::exp.find(it->first) != pdrh::distribution::exp.cend())
        {
            edges.insert(make_pair(it->first, gsl_ran_exponential(r, pdrh2box::node_to_interval(
                    pdrh::distribution::exp[it->first]).mid().leftBound())));
        }
        else if(pdrh::distribution::gamma.find(it->first) != pdrh::distribution::gamma.cend())
        {
            edges.insert(make_pair(it->first, gsl_ran_gamma(r, pdrh2box::node_to_interval(
                    pdrh::distribution::gamma[it->first].first).mid().leftBound(),
                                                            pdrh2box::node_to_interval(
                                                                    pdrh::distribution::gamma[it->first].second).mid().leftBound())));
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
            p_mass[i] = pdrh2box::node_to_interval(it2->second).mid().leftBound();
            i++;
        }
        // getting a pointer to the look up table
        gsl_ran_discrete_t* g = gsl_ran_discrete_preproc(mass_map.size(), p_mass);
        // getting a value index
        size_t index = gsl_ran_discrete(r, g);
        edges.insert(std::make_pair(it->first, pdrh2box::node_to_interval(p_value[index])));
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

double rnd::sobol_vector(box b)
{
    double vv;
    map<std::string, capd::interval> b_edges, edges;
    b_edges = b.get_map();

    for(auto it = b_edges.cbegin(); it != b_edges.cend(); it++)
    {
        //double value =capd::interval(it->second.leftBound() + v[i] * capd::intervals::width(it->second))
        double value = gsl_cdf_flat_Pinv(it->second.leftBound(), pdrh2box::node_to_interval(
                pdrh::distribution::uniform[it->first].first).leftBound(),
                                         pdrh2box::node_to_interval(
                                                 pdrh::distribution::uniform[it->first].second).leftBound());
        vv=value;
        //   edges.insert(make_pair(it->first, capd::interval(value,value)));
    }
    return vv;
}

box rnd::get_normal_random_sample(gsl_rng* r, box mu, box sigma)
{
    map<std::string, capd::interval> edges;
    for(auto it = pdrh::par_map.cbegin(); it != pdrh::par_map.cend(); it++)
    {
        if(it->second.first->value != it->second.second->value)
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
        else
        {
            edges.insert(make_pair(it->first, pdrh2box::node_to_interval(it->second.first).mid().leftBound()));
        }
    }
    return box(edges);
}

box rnd::get_beta_random_sample(gsl_rng* r, box alpha, box beta, box b)
{
    map<std::string, capd::interval> edges;
    map<std::string, capd::interval> b_map = b.get_map();
    for(auto it = b_map.cbegin(); it != b_map.cend(); it++)
    {
        double beta_dist_value = gsl_ran_beta(r, alpha.get_map()[it->first].leftBound(), beta.get_map()[it->first].leftBound());
        edges.insert(make_pair(it->first, capd::interval(it->second.leftBound() + beta_dist_value * capd::intervals::width(it->second))));
    }
    return box(edges);
}

double rnd::digamma(double x)
{
    return log(x)  - 1/(2*x)
                   - 1/(12*pow(x,2))
                   + 1/(120*pow(x,4))
                   - 1/(252*pow(x,6))
                   + 1/(240*pow(x,8))
                   - 5/(660*pow(x,10))
                   + 691/(32760*pow(x,12))
                   - 1/(12*pow(x,14));
}

pair<box, box> rnd::update_beta_dist(vector<box> q, box domain, box prev_alpha, box prev_beta)
{
    vector<box> q_norm;
    for(box b : q)
    {
        map<string, capd::interval> b_map = b.get_map();
        map<string, capd::interval> w_map, l_map;
        for(auto it = b_map.cbegin(); it != b_map.cend(); it++)
        {
            l_map.insert(make_pair(it->first, capd::interval(domain.get_map()[it->first].leftBound())));
            w_map.insert(make_pair(it->first, capd::intervals::width(domain.get_map()[it->first])));
        }
        box w(w_map), l(l_map);
        q_norm.push_back((b - l) / w);
        //cout << "initial box: " << b << " width: " << w << " left: " << l <<  " normalized box: " << (b - l) / w << endl;
    }

    map<string, capd::interval> n_map, one_map, zero_map;
    map<string, capd::interval> b_map = q.front().get_map();
    for(auto it = b_map.cbegin(); it != b_map.cend(); it++)
    {
        n_map.insert(make_pair(it->first, capd::interval(q_norm.size())));
        one_map.insert(make_pair(it->first, capd::interval(1)));
        zero_map.insert(make_pair(it->first, capd::interval(0)));
    }

    // initializing boxes
    box n(n_map), one(one_map), c1(zero_map), c2(zero_map);
    for(box b : q_norm)
    {
        c1 = c1 + box_factory::log(b);
        c2 = c2 + box_factory::log(one - b);
    }
    c1 = c1 / n;
    c2 = c2 / n;
    cout << "C1 = " << c1 << endl;
    cout << "C2 = " << c2 << endl;
    map<string, capd::interval> c_map = c1.get_map();
    map<string, capd::interval> alpha_map, beta_map;
    for(auto it = c_map.begin(); it != c_map.end(); it++)
    {
        pair<double, double> beta_params = rnd::solve_beta_system(c1.get_map()[it->first].mid().leftBound(),
                                                                  c2.get_map()[it->first].mid().leftBound(),
                                                                  prev_alpha.get_map()[it->first].mid().leftBound(),
                                                                  prev_beta.get_map()[it->first].mid().leftBound());
        alpha_map.insert(make_pair(it->first, beta_params.first));
        beta_map.insert(make_pair(it->first, beta_params.second));
    }
    return make_pair(box(alpha_map), box(beta_map));
}

int rnd::beta_system(const gsl_vector * x, void * param, gsl_vector * f)
{
    rnd::beta_system_params * params = (rnd::beta_system_params *)param;
    const double c1 = (params->c1);
    const double c2 = (params->c2);
    const double a = gsl_vector_get(x,0);
    const double b = gsl_vector_get(x,1);

    gsl_vector_set (f, 0, rnd::digamma(a) - rnd::digamma(a+b) - c1);
    gsl_vector_set (f, 1, rnd::digamma(b) - rnd::digamma(a+b) - c2);

    return GSL_SUCCESS;
}

pair<double, double> rnd::solve_beta_system(double c1, double c2, double prev_alpha, double prev_beta)
{
    const gsl_multiroot_fsolver_type * T;
    gsl_multiroot_fsolver * s;

    struct rnd::beta_system_params params = { c1, c2 };
    gsl_multiroot_function f;
    f.f = &beta_system;
    f.n = 2;
    f.params = &params;

    int status;
    size_t i, iter = 0;

    const size_t n = 2;

    gsl_vector *x = gsl_vector_alloc(n);

    gsl_vector_set (x, 0, prev_alpha);
    gsl_vector_set (x, 1, prev_beta);

    T = gsl_multiroot_fsolver_hybrids;
    s = gsl_multiroot_fsolver_alloc (T, n);
    gsl_multiroot_fsolver_set(s, &f, x);

    do
    {
        iter++;
        status = gsl_multiroot_fsolver_iterate (s);
        /* check if solver is stuck */
        if (status)
        {
            break;
        }
        status = gsl_multiroot_test_residual (s->f, 1e-7);
    }
    while (status == GSL_CONTINUE && iter < 1000);

    //cout << "status " << gsl_strerror (status) << endl;
    //cout << "alpha = " << gsl_vector_get(s->x, 0) << endl;
    //cout << "beta = " << gsl_vector_get(s->x, 1) << endl;

    double alpha = gsl_vector_get(s->x, 0);
    double beta = gsl_vector_get(s->x, 1);

    gsl_multiroot_fsolver_free (s);
    gsl_vector_free (x);

    return make_pair(alpha, beta);
}

box rnd::get_icdf(box b)
{
    map<std::string, capd::interval> b_edges, edges;
    b_edges = b.get_map();
    for(auto it = b_edges.cbegin(); it != b_edges.cend(); it++)
    {
        if(pdrh::distribution::uniform.find(it->first) != pdrh::distribution::uniform.cend())
        {
            double value = gsl_cdf_flat_Pinv(it->second.leftBound(), pdrh2box::node_to_interval(
                    pdrh::distribution::uniform[it->first].first).leftBound(),
                                             pdrh2box::node_to_interval(
                                                     pdrh::distribution::uniform[it->first].second).leftBound());
            //value += pdrh::node_to_interval(pdrh::distribution::normal[it->first].first).leftBound();

            edges.insert(make_pair(it->first, capd::interval(value,value)));
        }
        else if(pdrh::distribution::normal.find(it->first) != pdrh::distribution::normal.cend())
        {
            double value = gsl_cdf_gaussian_Pinv(it->second.leftBound(),
                                                 pdrh2box::node_to_interval(
                                                         pdrh::distribution::normal[it->first].second).leftBound());
            value += pdrh2box::node_to_interval(pdrh::distribution::normal[it->first].first).leftBound();
            edges.insert(make_pair(it->first, capd::interval(value,value)));
        }
        else if(pdrh::distribution::exp.find(it->first) != pdrh::distribution::exp.cend())
        {

        }
        else if(pdrh::distribution::gamma.find(it->first) != pdrh::distribution::gamma.cend())
        {

        }
        else
        {
            CLOG(ERROR, "ran_gen") << "Random number generator for the variable \"" << it->first << "\" is not supported";
        }
    }
    return box(edges);
}

box rnd::get_GPicdf(box b, box params)
{
    map<std::string, capd::interval> b_edges, edges;
    b_edges = b.get_map();
    for(auto it = b_edges.cbegin(); it != b_edges.cend(); it++)
    {
        if(pdrh::distribution::uniform.find(it->first) != pdrh::distribution::uniform.cend())
        {
            double value = gsl_cdf_flat_Pinv(it->second.leftBound(), pdrh2box::node_to_interval(
                    pdrh::distribution::uniform[it->first].first, {params}).leftBound(),
                                             pdrh2box::node_to_interval(
                                                     pdrh::distribution::uniform[it->first].second, {params}).leftBound());
            //value += pdrh::node_to_interval(pdrh::distribution::normal[it->first].first).leftBound();

            edges.insert(make_pair(it->first, capd::interval(value,value)));
        }
        else if(pdrh::distribution::normal.find(it->first) != pdrh::distribution::normal.cend())
        {
            double value = gsl_cdf_gaussian_Pinv(it->second.leftBound(),
                                                 pdrh2box::node_to_interval(
                                                         pdrh::distribution::normal[it->first].second, {params}).leftBound());
            value += pdrh2box::node_to_interval(pdrh::distribution::normal[it->first].first, {params}).leftBound();
            edges.insert(make_pair(it->first, capd::interval(value,value)));
        }
        else if(pdrh::distribution::exp.find(it->first) != pdrh::distribution::exp.cend())
        {

        }
        else if(pdrh::distribution::gamma.find(it->first) != pdrh::distribution::gamma.cend())
        {

        }
        else
        {
            CLOG(ERROR, "ran_gen") << "Random number generator for the variable \"" << it->first << "\" is not supported";
        }
    }
    return box(edges);
}

box rnd::get_randomuni_sample(gsl_rng* r)
{
    map<std::string, capd::interval> edges;
    // continuous distributions
    for(auto it = pdrh::rv_map.cbegin(); it != pdrh::rv_map.cend(); it++)
    {
        edges.insert(make_pair(it->first, gsl_rng_uniform(r)));
    }
    return box(edges);
}
/*
double rnd::find_sample_var(box b)
{
    map<std::string, capd::interval> b_edges, edges;
    b_edges = b.get_map();
    auto it = b_edges.cbegin();
    double value = it->second.leftBound();
    return value;
}
*/



















