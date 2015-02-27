// PartialSum class implements a partial sum
// used in 1/3 Simpson's rule for computing
// a definite integral of a bounded at least
// four times differentiable function.
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<iomanip>
#include<string>
#include "PartialSum.h"

using namespace std;
using namespace capd;

// Constructor of the class
//
// @param the name of the variable, 
// the integrated function and the interval	
PartialSum::PartialSum(string var, string fun, DInterval interval)
{
	this->var = var;
	this->fun = fun;
	this->interval = interval;
	this->value = calculate_value();
}

PartialSum::PartialSum(string var, string fun, DInterval interval, DInterval value)
{
	this->var = var;
	this->fun = fun;
	this->interval = interval;
	this->value = value;
}

// The method return the interval 
// where the partial sum is calculated
DInterval PartialSum::get_interval()
{
	return this->interval;
}

// The method returns the value of the partial sum
DInterval PartialSum::get_value()
{
	return this->value;
}

// The methods returns the name of the variable
string PartialSum::get_var()
{
	return this->var;
}

// The method returns the function
string PartialSum::get_fun()
{
	return this->fun;
}

// The method calculates a fourth derivative
// of the function (fun) on the interval
DInterval PartialSum::f4()
{
	DInterval v[] = {interval};
	IVector x(1, v);

	IJet jet(1, 1, 4);
	IMap fun_map = IMap("var:" + var + ";fun:" + fun + ";");
	fun_map.setDegree(4);
	fun_map(x, jet);

	return jet(0, 3) * 24;
}

// The method calculates the value 
// of the partial sum
DInterval PartialSum::calculate_value()
{
	IFunction fun_fun = IFunction("var:" + var + ";fun:" + fun + ";");
	DInterval res = (width(interval) / 6) * (fun_fun(interval.leftBound()) + 4 * fun_fun(interval.mid()) + fun_fun(interval.rightBound())) - (power(width(interval),5) / 2880) * f4();
	if(res.leftBound() < 0)
	{
		return DInterval(0, res.rightBound());
	}
	else
	{
		return res;
	}
}