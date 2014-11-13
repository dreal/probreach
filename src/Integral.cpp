// Integral class implements a verified integration
// procedure for an arbitrary four times differentiable 
// function using interval version of (1/3) Simpson's rule.
// The result of computation is an interval of arbitrarily
// small positive length containing the exact value of the
// definite integral
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#include "Integral.h"
#include "PartialSum.h"
#include "RV.h"
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<iomanip>
#include<string>

// Constructor of the class
//
// @param name of the variable, inegrated function,
// integration interval and precision
Integral::Integral(string var, string fun, DInterval interval, double precision)
{
	this->var = var;
	this->fun = fun;
	this->interval = interval;
	this->precision = precision;
	this->temp_vector.push_back(PartialSum(var, fun, DInterval(interval.leftBound(), interval.mid().rightBound())));
	this->temp_vector.push_back(PartialSum(var, fun, DInterval(interval.mid().leftBound(), interval.rightBound())));
	this->value = DInterval(0.0);
	calculate_value();
}

// The method retuns precision used for
// calculating the integral
double Integral::get_precision()
{
	return precision;
}

// The method returns the name of the variable
// with respect to which the integration is performed
string Integral::get_var()
{
	return var;
}

// The methods returns the integrated function
string Integral::get_fun()
{
	return fun;
}

// The method returns the value of the integral
DInterval Integral::get_value()
{
	return value;
}

// The method sets a precision on the
// integral calculation
//
// @param precision
void Integral::set_precision(double precision)
{
	this->precision = precision;
}

// The method returns partial sums forming
// the value of the integral
vector<PartialSum> Integral::get_partial_sums()
{
	return this->partial_sums;
}

// The method performs calculation of the integral
void Integral::calculate_value()
{
	while (temp_vector.size() > 0)
	{
		PartialSum p_sum = temp_vector.front();
		temp_vector.erase(temp_vector.begin());
	
		if (width(p_sum.get_value()) > precision * (width(p_sum.get_interval()) / width(interval)))
		{
			temp_vector.push_back(PartialSum(var, fun, DInterval(p_sum.get_interval().leftBound(), p_sum.get_interval().mid().rightBound())));
			temp_vector.push_back(PartialSum(var, fun, DInterval(p_sum.get_interval().mid().leftBound(), p_sum.get_interval().rightBound())));
		}
		else
		{
			partial_sums.push_back(p_sum);
			value += p_sum.get_value();
		}
	}
}
