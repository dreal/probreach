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
    std::map<std::string, std::string> c_map;
    std::map<std::string, std::map<capd::interval, capd::interval> > d_map;

    capd::interval volume(box);
    capd::interval measure(dd_box);
    capd::interval measure(rv_box);

}

#endif //PROBREACH_MEASURE_H
