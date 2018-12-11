//
// Created by fedor on 29/11/18.
//

#ifndef PROBREACH_NAIVE_IVP_H
#define PROBREACH_NAIVE_IVP_H

#include <string>
#include "node.h"
#include "model.h"

namespace naive
{
    std::map<std::string, double> solve_ivp(std::map<std::string, pdrh::node *>, std::map<std::string, double>, double, double);

    std::vector<std::map<std::string, double>> trajectory(std::map<std::string, pdrh::node*>, std::map<std::string, double>, double, double);

    std::vector<std::map<std::string, double>> trajectory(std::map<std::string, pdrh::node*>, std::map<std::string, double>, pdrh::node*, double, double);

    std::vector<std::vector<std::map<std::string, double>>> simulate(std::vector<pdrh::mode*>, std::map<std::string, pdrh::node*>, size_t, size_t, double);

}

#endif //PROBREACH_NAIVE_IVP_H
