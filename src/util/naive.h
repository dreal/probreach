//
// Created by fedor on 29/11/18.
//

#ifndef PROBREACH_NAIVE_IVP_H
#define PROBREACH_NAIVE_IVP_H

#include <string>

#include "model.h"
#include "node.h"

namespace naive {
std::map<std::string, double> solve_ivp(std::map<std::string, pdrh::node *>,
                                        std::map<std::string, double>, double,
                                        double);

std::vector<std::map<std::string, double>> trajectory(
    std::map<std::string, pdrh::node *>, std::map<std::string, double>, double,
    double);

void simulate(std::vector<pdrh::mode>, std::vector<pdrh::state>,
              std::vector<pdrh::state>, bool, size_t, size_t, size_t, size_t,
              std::ostream &);

void simulate(std::vector<pdrh::mode>, std::vector<pdrh::state>,
              std::vector<pdrh::state>, bool, size_t, size_t, size_t, double,
              std::ostream &);
}  // namespace naive

#endif  // PROBREACH_NAIVE_IVP_H
