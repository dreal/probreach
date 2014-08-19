/**
 * Distribution class declaration
 *
 * @author: Fedor Shmarov
 * @e-mail: f.shmarov@ncl.ac.uk
 */
 
#ifndef DISTRIBUTION_H  
#define DISTRIBUTION_H  

#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>

using namespace std;

/**
 * Returns probability density function for the normal random variable
 */
string normalString(string, double, double);

/**
 * Returns probability density function for the uniform random variable
 */
string uniformString(double, double);

#endif 