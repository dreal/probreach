// RVIntegral class implements a verified integration
// procedure for probability density funtion of an arbitrary
// continuous random variable. The result of computation is an
// interval of arbitrarily small positive length containing
// the exact value of the definite integral
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#ifndef RVINTEGRAL_H  
#define RVINTEGRAL_H  

#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include "PartialSum.h"
#include "RV.h"
#include "nRV.h"

using namespace std;
using namespace capd;

// RVIntegral class declaration 
class RVIntegral
{
	private:

		// Required width of the interval containing the value of the integral
		double precision;

		// Coefficient determining the bounds of the integration interval
		double coef;

		// Random variable
		RV* rv;

		// Integration interval
		DInterval interval;

		// The interval containing the exact value of the integral
		DInterval value;

		// List of partial sums forming the value of the
		// definite integral
		vector<PartialSum> partial_sums;

		// The method performs calculation of the integral
		void calculate_value();

	public:

		// Constructor of the class
		//
		// @param continuous random variable, coefficient
		// and precision
		RVIntegral(RV*, double, double);

		// The method returns the random variable which
		// probability density function is integrated
		RV* get_rv();

		// The method returns the value of the integral
		DInterval get_value();

		// The method returns the integration interval
		DInterval get_interval();

		// The method returns precision used for
		// calculating the integral
		double get_precision();

		// The method returns coefficient determining
		// the bounds of the integration interval
		double get_coef();

		// The method sets a precision on the
		// integral calculation
		//
		// @param precision
		void set_precision(double);

		// The method returns partial sums forming
		// the value of the integral
		vector<PartialSum> get_partial_sums();

		// The method sets a list of partial sums
		//
		// @param list of partial sums
		void set_partial_sums(vector<PartialSum>);
};
#endif 