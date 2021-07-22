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
    std::pair<capd::interval, std::vector<capd::interval>> integral(std::string, std::string, capd::interval, double);

    capd::interval volume(box);
    capd::interval p_measure(box, double);
    capd::interval p_measure(box);
    capd::interval p_dd_measure(box);

    capd::interval get_sample_prob(box, box, box);

    namespace compare_pairs
    {
        bool ascending(const pair<box, capd::interval> &, const pair<box, capd::interval> &);
        bool descending(const pair<box, capd::interval> &, const pair<box, capd::interval> &);
    }

    bool compare_boxes_by_p_measure(const box, const box);

    // obtain the partition of the parameter space
    std::vector<box> get_rv_partition();
    std::vector<box> get_dd_partition();

    double precision(double, int);

    namespace bounds
    {
        capd::interval gaussian(double, double, double);
        capd::interval exp(double, double);
        std::pair<capd::interval, std::vector<capd::interval>> pdf(std::string, std::string, capd::interval, double, double);
        box get_rv_domain();
    }

    namespace distribution
    {
        std::string gaussian(std::string, capd::interval, capd::interval);
        std::string uniform(capd::interval, capd::interval);
        std::string exp(std::string, capd::interval);
    }
}

#endif //PROBREACH_MEASURE_H
