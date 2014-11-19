// MulRVIntegral class implements a verified procedure for
// compuating a product of multiple RVIntegrals. 
// The result of computation is an interval of arbitrarily
// small positive length containing the exact value
// of the product of multiple RVIntegrals.
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#include "RVIntegral.h"
#include "MulRVIntegral.h"
#include "PartialSum.h"
#include "RV.h"
#include "nRV.h"
#include "Box.h"
#include "Integral.h"
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<iomanip>
#include<string>

// Constructor of the class
//
// @param vector of random variables, coefficient 
// and precision
MulRVIntegral::MulRVIntegral(vector<RV*> rv, double coef, double precision)
{
	this->rv = rv;
	this->precision = precision;
	this->coef = coef;
	calculate_value();
}

DInterval MulRVIntegral::calculate_box(Box box)
{
	DInterval prod = 1;
	for(int i = 0; i < box.get_dimension_size(); i++)
	{
		Integral integral(box.get_dimension(i).get_var(), box.get_dimension(i).get_fun(), box.get_dimension(i).get_interval(), precision);
		prod *= integral.get_value();
	}
	return prod;
}

// The method returns precision used for calculating the 
// product of the integrals
double MulRVIntegral::get_precision()
{
	return this->precision;
}

// The method returns the vector of random variables
vector<RV*> MulRVIntegral::get_rv()
{
	return this->rv;
}

// The method returns the value of the product of RVIntegrals.
DInterval MulRVIntegral::get_value()
{
	return this->value;
}

// The method sets a precision used for calculating 
// product of RVIntegrals
//
// @param precision
void MulRVIntegral::set_precision(double precision)
{
	this->precision = precision;
}

// The method returns coefficient determining
// the bounds of the integration interval in each RVIntegral
double MulRVIntegral::get_coef()
{
	return this->coef;
}

// The method returns partial sums forming
// the value of the product of RVIntegrals
vector< vector<PartialSum> > MulRVIntegral::get_partial_sums()
{
	return this->partial_sums;
}

// The method calculates a binomial coefficient
//
// @param parameters needed for calculating binomial coefficients
double MulRVIntegral::binomial_coef(int k, int n)
{
	double prod = 1;
	for(int i = 1; i <= k; i++)
	{
		prod = prod * ((double) (n + 1 - i) / (double) i);
	}
	return prod;
}

// The methods performs calculation of the local precision
// for calculating each integral in the product which guarantees
// the correctness of the computation
void MulRVIntegral::calculate_local_error()
{
	local_precision = precision;
	double sum = 0;
	int n = rv.size();
	for(int i = 0; i < n; i++)
	{
		sum = sum + binomial_coef(i + 1, n) * pow(local_precision, i + 1);
	}

	while (sum > precision)
	{
		local_precision = local_precision / 2;
		sum = 0;
		for(int i = 0; i < n; i++)
		{
			sum = sum + binomial_coef(i + 1, n) * pow(local_precision, i + 1);
		}
	}
}

// The method performs calculation of the product of RVIntegrals.
void MulRVIntegral::calculate_value()
{
	calculate_local_error();
	//cout << "local precision = " << local_precision << endl;
	//cout << "precision = " << precision << endl;
	DInterval integral_prod = 1;
	for(int i = 0; i < rv.size(); i++)
	{
		nRV* n_rv = dynamic_cast<nRV*>(rv.at(i));
		if(n_rv != 0)
		{
			RVIntegral rv_integral = RVIntegral(n_rv, coef, local_precision);
			partial_sums.push_back(rv_integral.get_partial_sums());
			integral_prod = integral_prod * rv_integral.get_value();
		}
	}
	value = integral_prod;
}

