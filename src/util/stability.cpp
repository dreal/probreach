//
// Created by fedor on 21/03/18.
//

#include "stability.h"
#include <cmath>
#include <algorithm>

using namespace std;

bool stability::jury_test(std::vector<double> poly)
{
    // getting the size of the polynomials
    size_t n = poly.size()-1;

    // condition 1
    if(abs(poly.back()) >= poly.front()) return false;

    // condition 2
    double res = 0;
    for(double value : poly)
    {
        res += value;
    }
    if(res <= 0) return false;

    // condition 3
    // n is even
    if(n % 2 == 0)
    {
        res = 0;
        double sign = 1;
        for(double value : poly)
        {
            res += sign*value;
            sign = -sign;
        }
        if(res <= 0) return false;
    }
    // n is odd
    else
    {
        res = 0;
        double sign = -1;
        for(double value : poly)
        {
            res += sign*value;
            sign = -sign;
        }
        if(res >= 0) return false;
    }

    // condition 4
    // reversing the table
    for(size_t j = 0; j < n - 2; j++)
    {
        size_t m = poly.size() - 1;
        vector<double> new_row;
        for(size_t i = 0; i < m; i++)
        {
            new_row.push_back(poly.at(m)*poly.at(i+1) - poly.at(0)*poly.at(m-1-i));
        }
        //reverse(new_row.begin(), new_row.end());
        if(abs(new_row.back()) <= abs(new_row.front())) return false;
        //reverse(new_row.begin(), new_row.end());
        poly = new_row;
    }

    return true;
}