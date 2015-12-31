//
// Created by fedor on 27/12/15.
//
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>

#include "measure.h"

std::map<std::string, std::string> measure::rv_map;

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