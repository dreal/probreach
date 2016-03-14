//
// Created by fedor on 29/12/15.
//
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include "box.h"

#ifndef PROBREACH_BOX_FACTORY_H
#define PROBREACH_BOX_FACTORY_H

namespace box_factory
{
    std::vector<box> cartesian_product(std::map<std::string, std::vector<capd::interval>>);
    std::vector<box> bisect(box);
    std::vector<box> bisect(box, std::map<std::string, capd::interval>);
    std::vector<box> merge(std::vector<box>);
    box merge(box, box);
}

#endif //PROBREACH_BOX_FACTORY_H
