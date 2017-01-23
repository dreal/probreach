//
// Created by fedor on 23/01/17.
//

#include <gtest/gtest.h>
#include "easylogging++.h"

INITIALIZE_EASYLOGGINGPP

int main(int argc, char **argv)
{
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}