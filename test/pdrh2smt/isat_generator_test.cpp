//
// Created by fedor on 01/03/17.
//

#include "node.h"
#include <gtest/gtest.h>
#include "model.h"
//#include "pdrhparser.hpp"
#include "isat_generator.h"

using namespace std;

TEST(generate_isat_model, normal)
{
  model m = parse_pdrh("/home/fedor/isat/model/cars/stop-nonlinear.pdrh");
  cout << isat_generator::generate_isat_model(m);
}