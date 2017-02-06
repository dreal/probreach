//
// Created by fedor on 06/02/17.
//

#include "node.h"
#include <gtest/gtest.h>
#include "pdrhparser.hpp"
#include "model.h"

using namespace std;

extern model parse_pdrh(string);

TEST(pdrhparser, normal)
{
    model m = parse_pdrh("/home/fedor/probreach/model/anesthesia/anesthesia.drh");
}