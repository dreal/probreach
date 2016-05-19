//
// Created by fedor on 26/02/16.
//

#ifndef PROBREACH_DREAL_WRAPPER_H
#define PROBREACH_DREAL_WRAPPER_H
#include<iostream>
#include <capd/capdlib.h>
#include <capd/intervals/lib.h>

namespace dreal
{
    extern std::vector<std::string> sat_answers;
    extern std::vector<std::string> unsat_answers;

    int execute(std::string, std::string, std::string);
    int parse_output(std::string);
    std::map<std::string, capd::interval> parse_model();
}

#endif //PROBREACH_DREAL_WRAPPER_H
