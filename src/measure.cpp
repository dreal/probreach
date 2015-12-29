//
// Created by fedor on 27/12/15.
//
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>

#include "measure.h"
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
