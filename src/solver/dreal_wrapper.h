//
// Created by fedor on 26/02/16.
//

#ifndef PROBREACH_DREAL_WRAPPER_H
#define PROBREACH_DREAL_WRAPPER_H
#include<iostream>
#include <vector>
#include <capd/capdlib.h>
#include "util/box.h"
//#include <capd/intervals/lib.h>

using namespace std;

namespace dreal
{

    int execute(string, string, string);
    //int parse_output(std::string);
    box parse_model(string);
}

#endif //PROBREACH_DREAL_WRAPPER_H
