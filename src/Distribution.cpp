/**
 * Class for generating probability density functions 
 * for commonly used distributions.
 *
 * @author: Fedor Shmarov
 * @e-mail: f.shmarov@ncl.ac.uk
 */
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include "Distribution.h"

using namespace std;

/**
 * Returns probability density function for the normal random variable
 *
 * @param var is the name of the variable, mean is the mean of the normal random variable
 * and deviation is a standard deviation of the normal random variable
 *
 * @return probability density function
 */
string normalString(string var, double mean, double deviation)
{
	stringstream s;
	s 	<< "(1 / (" << deviation << " * sqrt(2 * 3.14159265359)) * exp(- (( " << var << " - " << mean 
		<<	") * (" << var << " - " << mean << ")) / (2 * " << deviation << " * " << deviation << ")))";
	return s.str();
}

/**
 * Returns probability density function for the uniform random variable
 *
 * @param left is the left bound of uniform random variable, right is the right bound of uniform random variable
 *
 * @return probability density function
 */
string uniformString(double left, double right)
{
	stringstream s;
	s 	<< "1 / (" << right - left << ")";
	return s.str();
}