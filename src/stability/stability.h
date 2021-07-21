//
// Created by fedor on 21/03/18.
//

#include <iostream>
#include <map>
#include <vector>

#include "box.h"
#include "model.h"

#ifndef PROBREACH_STABILITY_H
#define PROBREACH_STABILITY_H

namespace stability {

// first parameter - odes, second parameter - time sampling, third parameter -
// initial condition, fourth parameter - controller parameters
bool is_stable(std::map<std::string, pdrh::node*>, double, box, box);

// performs stability check using jury test for a given polynomial
bool jury_test(std::vector<double>);

}  // namespace stability

#endif  // PROBREACH_STABILITY_H
