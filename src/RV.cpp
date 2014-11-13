// RV class implements a generic random variable.
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#include<string>
#include<sstream>
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include "RV.h"

using namespace std;

// Class contructor
// 
// @param name of the random variable in a string format
RV::RV(string var)
{
	this->var = var;
}

// The method returns a notation of the random variable
// in defined form (e.g. N(0,1) for a random variable with 
// mean = 0 and standard deviation = 1)
string RV::get_notation()
{
	return this->notation;
}

// The method returns the name of the random variable
// in a string format
string RV::get_var()
{
	return this->var;
}

// The method returns the probability density
// function of the random variable in a string format
string RV::get_pdf()
{
	return this->pdf;
}

// The method returns the bounds set on the random
// variable (needed to support integral computation)
DInterval RV::get_domain()
{
	return this->domain;
}

// The method sets a notation for the defined random
// variable
//
// @param notation of the random variable
void RV::set_notation(string notation)
{
	this->notation = notation;
}

// The method sets a probabilty density function
// for the defined random variable
//
// @param notation of the random variable
void RV::set_pdf(string pdf)
{
	this->pdf = pdf;
}

// The method sets a bounded domain for the defined
// random variable (in order to support the integral
// computation)
//
// @param bounded domain of the random variable
void RV::set_domain(DInterval domain)
{
	this->domain = domain;
}

// Class destructor
RV::~RV()
{
	
}
