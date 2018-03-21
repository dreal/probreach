//
// Created by fedor on 21/03/18.
//

#include <iostream>
#include <vector>


#ifndef PROBREACH_STABILITY_H
#define PROBREACH_STABILITY_H



namespace stability
{
    // performs stability check using jury test for a given polynomial
    bool jury_test(std::vector<double>);
}

#endif //PROBREACH_STABILITY_H
