// nRV class extends RV class and  
// implements a normal random variable.
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#include<string>
#include<iostream>
#include<sstream>
#include "nRV.h"
#include "RV.h"

using namespace std;

// Class contructor
// 
// @param name of the random variable in a string format, 
// mean and standard deviation
nRV::nRV(string var, double mean, double deviation):RV(var)
{
	this->mean = mean;
	this->deviation = deviation;
	set_notation(generate_notation());
	set_pdf(generate_pdf(var));
	set_domain(DInterval(mean - deviation, mean + deviation));
}

// The method generates a notation
// of the form N(mean, deviation)
string nRV::generate_notation()
{
	stringstream s;
	s << "N(" << mean << "," << deviation << ")";
	return s.str();
}

// The method generates an probability 
// density function in a string format
string nRV::generate_pdf(string var)
{
	stringstream s;
	s 	<< "(1 / (" << deviation << " * sqrt(2 * 3.14159265359)) * exp(- (( " << var << " - " << mean 
		<<	") * (" << var << " - " << mean << ")) / (2 * " << deviation << " * " << deviation << ")))";
	return s.str();
}

// The method returns the value of the mean
double nRV::get_mean()
{
	return this->mean;
}

// The method returns the value of the standard deviation
double nRV::get_deviation()
{
	return this->deviation;
}
