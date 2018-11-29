//
// Created by fedor on 29/11/18.
//

#ifndef PROBREACH_NAIVE_IVP_H
#define PROBREACH_NAIVE_IVP_H

#include <string>
#include "node.h"

namespace naive_ivp
{
    std::map<std::string, double> solve(std::map<std::string, pdrh::node*>, std::map<std::string, double>, std::map<std::string, double>, double, double);
    std::vector<std::map<std::string, double>> trajectory(std::map<std::string, pdrh::node*>, std::map<std::string, double>, std::map<std::string, double>, double, double);
}

#endif //PROBREACH_NAIVE_IVP_H
