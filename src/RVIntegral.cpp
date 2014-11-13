// RVIntegral class implements a verified integration
// procedure for probability density funtion of an arbitrary
// continuous random variable. The result of computation is an
// interval of arbitrarily small positive length containing
// the exact value of the definite integral
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#include "RVIntegral.h"
#include "Integral.h"
#include "PartialSum.h"
#include "RV.h"
#include "nRV.h"
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<iomanip>
#include<string>

// Constructor of the class
//
// @param continuous random variable, coefficient
// and precision
RVIntegral::RVIntegral(RV* rv, double coef, double precision)
{
	this->rv = rv;
	this->precision = precision;
	this->coef = coef;
	calculate_value();
}

// The method retuns precision used for
// calculating the integral
double RVIntegral::get_precision()
{
	return this->precision;
}

// The method returns the random variable which
// probability density function is integrated
RV* RVIntegral::get_rv()
{
	return this->rv;
}

// The method returns the value of the integral
DInterval RVIntegral::get_value()
{
	return this->value;
}

// The method sets a precision on the
// integral calculation
//
// @param precision
void RVIntegral::set_precision(double precision)
{
	this->precision = precision;
}

// The method retuns coefficient determining
// the bounds of the integration interval
double RVIntegral::get_coef()
{
	return this->coef;
}

// The method returns partial sums forming
// the value of the integral
vector<PartialSum> RVIntegral::get_partial_sums()
{
	return this->partial_sums;
}

// The method sets a list of partial sums
//
// @param list of partial sums
void RVIntegral::set_partial_sums(vector<PartialSum> partial_sums)
{
	this->partial_sums = partial_sums;
}

// The method performs calculation of the integral
void RVIntegral::calculate_value()
{
	nRV* n_rv = dynamic_cast<nRV*>(rv);
	if(n_rv != 0)
	{
		Integral integral = Integral(n_rv->get_var(), n_rv->get_pdf(), n_rv->get_domain(), (1-coef) * precision);
		DInterval integral_value = integral.get_value();
		while(1 - integral_value.leftBound() > coef * precision)
		{
			n_rv->set_domain(DInterval(n_rv->get_domain().leftBound() - n_rv->get_deviation(), n_rv->get_domain().rightBound() + n_rv->get_deviation()));
			integral = Integral(n_rv->get_var(), n_rv->get_pdf(), n_rv->get_domain(), (1-coef) * precision);
			integral_value = integral.get_value();
		}
		this->value = integral_value;
		this->partial_sums = integral.get_partial_sums();
		return;
	}
}