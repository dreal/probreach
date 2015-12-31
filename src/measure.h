//
// Created by fedor on 27/12/15.
//
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include "box.h"

#ifndef PROBREACH_MEASURE_H
#define PROBREACH_MEASURE_H

namespace measure
{
    extern std::map<std::string, std::string> rv_map;
    extern std::map<std::string, std::map<capd::interval, double> > dd_map;

    std::pair<capd::interval, std::vector<capd::interval>> integral(std::string, std::string, capd::interval, double);

    capd::interval volume(box);
    std::vector<rv_box> partition(rv_box, double);
    capd::interval p_measure(rv_box, double);
    capd::interval p_measure(dd_box, double);

    double binomial(int, int);
    double precision(double, int);

    namespace bounds
    {
        capd::interval gaussian(double, double, double);
        capd::interval exp(double, double);
    }

    namespace distribution
    {
        std::string gaussian(std::string, double, double);
        std::string uniform(std::string, double, double);
        std::string exp(std::string, double);
    }
}

#endif //PROBREACH_MEASURE_H
