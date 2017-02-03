//
// Created by fedor on 04/03/16.
//

#ifndef PROBREACH_CSVPARSER_H
#define PROBREACH_CSVPARSER_H

#include <capd/intervals/lib.h>
#include <map>
#include "pdrh.h"

using namespace std;

namespace csvparser
{
    map<string, vector<pair<pdrh::node*, pdrh::node*>>> parse(string);
}

#endif //PROBREACH_CSVPARSER_H


