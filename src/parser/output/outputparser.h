//
// Created by fedor on 20/01/17.
//

#ifndef PROBREACH_OUTPUTPARSER_H
#define PROBREACH_OUTPUTPARSER_H

#include <capd/intervals/lib.h>

#include <map>

#include "box.h"

using namespace std;

namespace outputparser {
map<box, capd::interval> parse_p_map(string);
}

#endif  // PROBREACH_OUTPUTPARSER_H
