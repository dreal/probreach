#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include "Distribution.h"

using namespace std;

string normalString(string var, double mean, double deviation)
{
	stringstream s;
	s 	<< "(1 / (" << deviation << " * sqrt(2 * 3.14159265359)) * exp(- (( " << var << " - " << mean 
		<<	") * (" << var << " - " << mean << ")) / (2 * " << deviation << " * " << deviation << ")))";
	return s.str();
}

string uniformString(double left, double right)
{
	stringstream s;
	s 	<< "1 / (" << right - left << ")";
	return s.str();
}