//
// Created by fedor on 06/02/17.
//

#include "node.h"
#include <gtest/gtest.h>
#include "model.h"
//#include "pdrhparser.hpp"
#include "smt2generator.h"

using namespace std;

TEST(pdrhparser, normal)
{
    //model m = parse_pdrh("/home/fedor/probreach/model/anesthesia/anesthesia.drh");
    model m = parse_pdrh("/home/fedor/probreach/model/cannon-ball/cannon-ball.drh");

//    cout << "depth 0" << endl;
//    cout << smt2generator::generate_reachability_formula(m, 0) << endl;
//
//    cout << "depth 1" << endl;
//    cout << smt2generator::generate_reachability_formula(m, 1) << endl;
//
//    cout << "depth 2" << endl;
//    cout << smt2generator::generate_reachability_formula(m, 2) << endl;
//
//    cout << "depth 3" << endl;
//    cout << smt2generator::generate_reachability_formula(m, 3) << endl;
//
//    cout << "depth 4" << endl;
//    cout << smt2generator::generate_reachability_formula(m, 4) << endl;
}