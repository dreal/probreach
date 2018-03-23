//
// Created by fedor on 21/03/18.
//

#include <iostream>
#include <vector>
#include <map>
#include "pdrh.h"


#ifndef PROBREACH_STABILITY_H
#define PROBREACH_STABILITY_H



namespace stability
{
    // performs stability check using jury test for a given polynomial
    bool jury_test(std::vector<double>);

    // first parameter - odes, second parameter - time sampling, third parameter - initial condition, fourth parameter - controller parameters
    std::vector<double> get_char_poly(std::map<std::string, pdrh::node*>, double, box, vector<box>);
}

#endif //PROBREACH_STABILITY_H
