//
// Created by fedor on 27/12/15.
//
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include "box.h"
#include "model.h"

#ifndef PROBREACH_MEASURE_H
#define PROBREACH_MEASURE_H

namespace measure
{

    std::pair<capd::interval, std::vector<capd::interval>> integral(std::string, std::string, capd::interval, double);

    capd::interval volume(box);
    capd::interval p_measure(box, double);
    capd::interval p_measure(box);
    std::vector<box> partition(box, double);

    std::vector<rv_box> partition(rv_box, double);
    capd::interval p_measure(rv_box, double);
    capd::interval p_measure(rv_box);
    capd::interval p_measure(dd_box);

    // obtain the partition of the parameter space
    std::vector<box> get_rv_partition();
    std::vector<box> get_dd_partition();

    double binomial(int, int);
    double precision(double, int);

    namespace bounds
    {
        capd::interval gaussian(double, double, double);
        capd::interval exp(double, double);
        std::pair<capd::interval, std::vector<capd::interval>> pdf(std::string, std::string, capd::interval, double, double);
        box get_rv_domain();
        void update();
    }

    namespace distribution
    {
        std::string gaussian(std::string, double, double);
        std::string uniform(double, double);
        std::string exp(std::string, double);

        //pdrh::node* gaussian(std::string, double, double);
        //pdrh::node* uniform(double, double);
        //pdrh::node* exp(std::string, double);
    }
}

#endif //PROBREACH_MEASURE_H
