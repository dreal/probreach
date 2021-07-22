//
// Created by fedor on 23/01/17.
//

#include <gtest/gtest.h>
#include "stability.h"

using namespace std;

TEST(jury_test, stable)
{
    vector<double> poly = {1, -1.2, 0.07, 0.3, -0.08};

    EXPECT_TRUE(stability::jury_test(poly));

    poly = {1, -9.21267237083505, 38.4437900689364, -95.8977134162288, 158.852608864770,
              -183.430069334737, 150.625415071236, -87.9336263830034, 35.7547070801493,
              -9.64046962920989, 1.55072243834666, -0.112692258706653, -1.30717570879249e-07};

    EXPECT_TRUE(stability::jury_test(poly));

}

