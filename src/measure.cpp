//
// Created by fedor on 27/12/15.
//
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<ibex.h>
#include "measure.h"
#include "box_factory.h"

std::map<std::string, std::string> measure::rv_map;
std::map<std::string, std::map<capd::interval, capd::interval>> measure::dd_map;

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
    int res = 1;
    for(int i = 1; i <= k; i++)
    {
        res *= (double) (n + 1 - i) / (double) i;
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
        if(measure::rv_map.find(it->first) != measure::rv_map.cend())
        {
            std::pair<capd::interval, std::vector<capd::interval>> itg = measure::integral(it->first, measure::rv_map[it->first], it->second, measure::precision(e, edges.size()));
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
        if(measure::rv_map.find(it->first) != measure::rv_map.cend())
        {
            res *= measure::integral(it->first, measure::rv_map[it->first], it->second, measure::precision(e, edges.size())).first;
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

capd::interval measure::p_measure(dd_box b)
{
    std::map<std::string, capd::interval> edges = b.get_map();
    capd::interval res(1.0);
    for(auto it = edges.cbegin(); it != edges.cend(); it++)
    {
        if(measure::dd_map.find(it->first) != measure::dd_map.cend())
        {
            if(measure::dd_map.at(it->first).find(it->second) != measure::dd_map.at(it->first).cend())
            {
                res *= dd_map.at(it->first).at(it->second);
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
    double k = 0.1;
    capd::interval i(mu - 3 * sigma, mu + 3 * sigma);
    std::pair<capd::interval, std::vector<capd::interval>> itg = measure::integral("x", measure::distribution::gaussian("x", mu, sigma), i, (1-k) * e);
    while(1 - itg.first.leftBound() > k * e)
    {
        i = capd::interval(i.leftBound() - sigma, i.rightBound() + sigma);
        itg = measure::integral("x", measure::distribution::gaussian("x", mu, sigma), i, (1-k) * e);
    }
    return i;
}

capd::interval measure::bounds::exp(double lambda, double e)
{
    double k = 0.1;
    capd::interval i(0, 3 / lambda);
    std::pair<capd::interval, std::vector<capd::interval>> itg = measure::integral("x", measure::distribution::exp("x", lambda), i, (1-k) * e);
    while(1 - itg.first.leftBound() > k * e)
    {
        i = capd::interval(0, i.rightBound() + (1 / lambda));
        itg = measure::integral("x", measure::distribution::exp("x", lambda), i, (1-k) * e);
    }
    return i;
}

std::string measure::distribution::gaussian(std::string var, double mu, double sigma)
{
    std::stringstream s;
    s 	<< "(1 / (" << sigma << " * sqrt(2 * 3.14159265359)) * exp(- (( " << var << " - " << mu
    <<	") * (" << var << " - " << mu << ")) / (2 * " << sigma << " * " << sigma << ")))";
    return s.str();
}

std::string measure::distribution::exp(std::string var, double lambda)
{
    std::stringstream s;
    s << lambda << " * exp(" << "-" << lambda << " * " << var << ")";
    return s.str();
}

std::string measure::distribution::uniform(std::string var, double a, double b)
{
    std::stringstream s;
    s << "1 / (" << b << " - " << a << ")";
    return s.str();
}