//
// Created by fedor on 27/12/15.
//

#include "measure.h"
/**
 * Calculates volume of the box
 */
capd::interval measure::volume(box b)
{
    std::vector<capd::interval> i = b.get_intervals();
    capd::interval v(1.0);
    for(auto it = i.cbegin(); it != i.cend(); it++)
    {
        v *= capd::filib::width(*it);
    }
    return v;
}
