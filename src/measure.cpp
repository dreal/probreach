//
// Created by fedor on 27/12/15.
//
#include<capd/capdlib.h>
#include<ibex.h>
#include<tuple>
#include "measure.h"
#include "box_factory.h"
#include "model.h"
#include "pdrh_config.h"

std::pair<capd::interval, std::vector<capd::interval>> measure::integral(std::string var, std::string fun, capd::interval it, double e)
{
    std::vector<capd::interval> stack,partition;
    capd::interval value(0);
    stack.push_back(it);

    while(!stack.empty())
    {
        capd::interval i = stack.front();
        stack.erase(stack.begin());

        capd::interval v[] = {i};
        capd::IVector x(1, v);
        capd::IJet jet(1, 1, 4);
        capd::IMap f_map("var:" + var + ";fun:" + fun + ";");
        f_map.setDegree(4);
        f_map(x, jet);
        capd::interval f4 = jet(0, 3) * 24;
        capd::IFunction fun_fun("var:" + var + ";fun:" + fun + ";");
        capd::interval itg = (capd::intervals::width(i) / 6) * (fun_fun(i.leftBound()) + 4 * fun_fun(i.mid()) +
                                                                fun_fun(i.rightBound())) - (power(capd::intervals::width(i),5) / 2880) * f4;
        if(capd::intervals::width(itg) <= e * (capd::intervals::width(i) / capd::intervals::width(it)))
        {
            partition.push_back(i);
            value += itg;
        }
        else
        {
            stack.push_back(capd::interval(i.leftBound(), i.mid().rightBound()));
            stack.push_back(capd::interval(i.mid().leftBound(), i.rightBound()));
        }
    }
    return make_pair(value, partition);
}

/**
 * Calculates volume of the box
 */
capd::interval measure::volume(box b)
{
    std::vector<capd::interval> i = b.get_intervals();
    capd::interval v(1.0);
    for(capd::interval it : i)
    {
        v *= capd::intervals::width(it);
    }
    return v;
}

double measure::binomial(int k, int n)
{
    double res = 1;
    for(int i = 1; i <= k; i++)
    {
        res *= (double) (n + 1 - i) / (double) i;
        //std::cout << "res (i=" << i << ") and (k=" << k << ") = " << res << std::endl;
    }
    return res;
}

double measure::precision(double e, int n)
{
    std::stringstream s;
    for(int i = 0; i < n; i++)
    {
        s << measure::binomial(i + 1, n) << "*e^" << i + 1 << "+";
    }
    s << "-" << e;
    //std::cout << "expression: " << s.str() << std::endl;
    ibex::Function f("e", s.str().c_str());
    ibex::IntervalVector b(1, ibex::Interval(0, 1));
    ibex::CtcFwdBwd c(f);
    ibex::CtcFixPoint fp(c, e);
    fp.contract(b);

    return b[0].lb();
}

std::vector<rv_box> measure::partition(rv_box b, double e)
{
    std::map<std::string, capd::interval> edges = b.get_map();
    std::map<std::string, std::vector<capd::interval>> m;
    for(auto it = edges.cbegin(); it != edges.cend(); it++)
    {
        if(pdrh::rv_map.find(it->first) != pdrh::rv_map.cend())
        {
            std::pair<capd::interval, std::vector<capd::interval>> itg = measure::integral(it->first, std::get<0>(pdrh::rv_map[it->first]), std::get<1>(pdrh::rv_map[it->first]), measure::precision(e, edges.size()));
            //std::pair<capd::interval, std::vector<capd::interval>> itg = measure::integral(it->first, measure::rv_map[it->first], it->second, power(e, 1/edges.size()));
            m.insert(make_pair(it->first, itg.second));
        }
        else
        {
            std::stringstream s;
            s << "Measure for " << it->first << " is undefined";
            throw std::invalid_argument(s.str());
        }
    }
    std::vector<box> p = box_factory::cartesian_product(m);
    std::vector<rv_box> rv_p(p.cbegin(), p.cend());
    return rv_p;
}

capd::interval measure::p_measure(rv_box b, double e)
{
    std::map<std::string, capd::interval> edges = b.get_map();
    capd::interval res(1.0);
    for(auto it = edges.cbegin(); it != edges.cend(); it++)
    {
        if(pdrh::rv_map.find(it->first) != pdrh::rv_map.cend())
        {
            res *= measure::integral(it->first, std::get<0>(pdrh::rv_map[it->first]), it->second, measure::precision(e, edges.size())).first;
            //res *= measure::integral(it->first, measure::rv_map[it->first], it->second, power(e, 1/edges.size())).first;
        }
        else
        {
            std::stringstream s;
            s << "Measure for " << it->first << " is undefined";
            throw std::invalid_argument(s.str());
        }
    }
    return res;
}

capd::interval measure::p_measure(box b, double e)
{
    std::map<std::string, capd::interval> edges = b.get_map();
    capd::interval res(1.0);
    for(auto it = edges.cbegin(); it != edges.cend(); it++)
    {
        if(pdrh::rv_map.find(it->first) != pdrh::rv_map.cend())
        {
            res *= measure::integral(it->first, std::get<0>(pdrh::rv_map[it->first]), it->second, measure::precision(e, edges.size())).first;
            //res *= measure::integral(it->first, measure::rv_map[it->first], it->second, power(e, 1/edges.size())).first;
        }
        else if(pdrh::dd_map.find(it->first) != pdrh::dd_map.cend())
        {
            if(pdrh::dd_map.at(it->first).find(it->second) != pdrh::dd_map.at(it->first).cend())
            {
                res *= pdrh::dd_map.at(it->first).at(it->second);
            }
            else
            {
                std::stringstream s;
                s << "Measure for " << it->first << " = " << it->second << " is undefined";
                throw std::invalid_argument(s.str());
            }
        }
        else
        {
            std::stringstream s;
            s << "Measure for " << it->first << " is undefined";
            throw std::invalid_argument(s.str());
        }
    }
    return res;
}

capd::interval measure::p_measure(box b)
{
    return p_measure(b, global_config.precision_prob);
}

std::vector<box> measure::partition(box b, double e)
{
    std::map<std::string, capd::interval> edges = b.get_map();
    std::map<std::string, std::vector<capd::interval>> m;
    for(auto it = edges.cbegin(); it != edges.cend(); it++)
    {
        if(pdrh::rv_map.find(it->first) != pdrh::rv_map.cend())
        {
            std::pair<capd::interval, std::vector<capd::interval>> itg = measure::integral(it->first, std::get<0>(pdrh::rv_map[it->first]), std::get<1>(pdrh::rv_map[it->first]), measure::precision(e, edges.size()));
            m.insert(make_pair(it->first, itg.second));
        }
        else
        {
            std::stringstream s;
            s << "Measure for " << it->first << " is undefined";
            throw std::invalid_argument(s.str());
        }
    }
    return box_factory::cartesian_product(m);
}

capd::interval measure::p_measure(rv_box b)
{
    return measure::p_measure(b, global_config.precision_prob);
}

capd::interval measure::p_measure(dd_box b)
{
    std::map<std::string, capd::interval> edges = b.get_map();
    capd::interval res(1.0);
    for(auto it = edges.cbegin(); it != edges.cend(); it++)
    {
        if(pdrh::dd_map.find(it->first) != pdrh::dd_map.cend())
        {
            if(pdrh::dd_map.at(it->first).find(it->second) != pdrh::dd_map.at(it->first).cend())
            {
                res *= pdrh::dd_map.at(it->first).at(it->second);
            }
            else
            {
                std::stringstream s;
                s << "Measure for " << it->first << " = " << it->second << " is undefined";
                throw std::invalid_argument(s.str());
            }
        }
        else
        {
            std::stringstream s;
            s << "Measure for " << it->first << " is undefined";
            throw std::invalid_argument(s.str());
        }
    }
    return res;
}

capd::interval measure::bounds::gaussian(double mu, double sigma, double e)
{
    capd::interval i(mu - 3 * sigma, mu + 3 * sigma);
    std::pair<capd::interval, std::vector<capd::interval>> itg = measure::integral("x", measure::distribution::gaussian("x", mu, sigma), i, (1 - global_config.integral_inf_coeff) * e);
    while(1 - itg.first.leftBound() > global_config.integral_inf_coeff * e)
    {
        i = capd::interval(i.leftBound() - sigma, i.rightBound() + sigma);
        itg = measure::integral("x", measure::distribution::gaussian("x", mu, sigma), i, (1 - global_config.integral_inf_coeff) * e);
    }
    return i;
}

capd::interval measure::bounds::exp(double lambda, double e)
{
    capd::interval i(0, 3 / lambda);
    std::pair<capd::interval, std::vector<capd::interval>> itg = measure::integral("x", measure::distribution::exp("x", lambda), i, (1-global_config.integral_inf_coeff) * e);
    while(1 - itg.first.leftBound() > global_config.integral_inf_coeff * e)
    {
        i = capd::interval(0, i.rightBound() + (1 / lambda));
        itg = measure::integral("x", measure::distribution::exp("x", lambda), i, (1-global_config.integral_inf_coeff) * e);
    }
    return i;
}

std::pair<capd::interval, std::vector<capd::interval>> measure::bounds::pdf(std::string var, std::string pdf, capd::interval domain, double start, double e)
{
    // checking if the starting point is in the domain
    if(!domain.contains(start))
    {
        std::stringstream s;
        s << "starting point " << start << " does not belong to the domain " << domain << " while trying to find pdf bounds";
        throw std::invalid_argument(s.str());
    }
    // initializing the interval
    capd::interval res = capd::interval(start);
    while(true)
    {
        // setting the interval
        res = capd::interval(res.leftBound() - global_config.integral_pdf_step, res.rightBound() + global_config.integral_pdf_step);
        //std::cout << res << std::endl;
        // adjusting left bound of the initial interval
        if(res.leftBound() < domain.leftBound())
        {
            res = capd::interval(domain.leftBound(), res.rightBound());
        }
        // adjusting right bound of the initial interval
        if(res.rightBound() > domain.rightBound())
        {
            res = capd::interval(res.leftBound(), domain.rightBound());
        }
        // calculating integral
        std::pair<capd::interval, std::vector<capd::interval>> itg = measure::integral(var, pdf, res, e);
        // checking if the value of the integral satisfies the condition
        if(1 - itg.first.leftBound() < e * global_config.integral_inf_coeff)
        {
            return make_pair(res, itg.second);
        }
        // the bound was reached but the precision value is not reached
        else if(res == domain)
        {
            std::stringstream s;
            s << "Unable to bound the integral of the pdf on " << domain << " by the value " << e * global_config.integral_inf_coeff;
            throw std::out_of_range(s.str());
        }
    }
}

std::string measure::distribution::gaussian(std::string var, capd::interval mu, capd::interval sigma)
{
    std::stringstream s;
    s 	<< "(1 / (" << sigma.leftBound() << " * sqrt(2 * 3.14159265359)) * exp(- (( " << var << " - " << mu.leftBound()
    <<	") * (" << var << " - " << mu.leftBound() << ")) / (2 * " << sigma.leftBound() << " * " << sigma.leftBound() << ")))";
    return s.str();
}

// check whether implemented correctly
std::string measure::distribution::exp(std::string var, capd::interval lambda)
{
    std::stringstream s;
    s << lambda.leftBound() << " * exp(" << "-" << lambda.leftBound() << " * " << var << ")";
    return s.str();
}

std::string measure::distribution::uniform(capd::interval a, capd::interval b)
{
    std::stringstream s;
    s << "1 / (" << b.leftBound() << " - " << a.leftBound() << ")";
    return s.str();
}

std::vector<box> measure::get_rv_partition()
{
    std::map<std::string, std::vector<capd::interval>> partition_map;
    for(auto it = pdrh::rv_map.cbegin(); it != pdrh::rv_map.cend(); it++)
    {
        std::pair<capd::interval, std::vector<capd::interval>> bound = measure::bounds::pdf(it->first,
                                                                        std::get<0>(it->second), std::get<1>(it->second), std::get<2>(it->second),
                                                                                 measure::precision(global_config.precision_prob, pdrh::rv_map.size()));

        std::tuple<std::string, capd::interval, double> new_tuple = std::make_tuple(std::get<0>(it->second), bound.first, std::get<2>(it->second));
        pdrh::rv_map[it->first] = new_tuple;
        // updating partition map
        partition_map.insert(std::make_pair(it->first, bound.second));
    }
    return box_factory::cartesian_product(partition_map);
}

std::vector<box> measure::get_dd_partition()
{
    std::map<std::string, std::vector<capd::interval>> m;
    for(auto it = pdrh::dd_map.cbegin(); it != pdrh::dd_map.cend(); it++)
    {
        std::vector<capd::interval> args;
        for(auto it2 = it->second.cbegin(); it2 != it->second.cend(); it2++)
        {
            args.push_back(it2->first);
        }
        m.insert(make_pair(it->first, args));
    }
    return box_factory::cartesian_product(m);
}

box measure::bounds::get_rv_domain()
{
    std::map<std::string, std::vector<capd::interval>> domain_map;
    for(auto it = pdrh::rv_map.cbegin(); it != pdrh::rv_map.cend(); it++)
    {
        std::vector<capd::interval> tmp;
        tmp.push_back(std::get<1>(it->second));
        domain_map.insert(std::make_pair(it->first, tmp));
    }
    std::vector<box> domain = box_factory::cartesian_product(domain_map);
    return domain.front();
}








