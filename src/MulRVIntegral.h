// MulRVIntegral class implements a verified procedure for
// compuating a product of multiple RVIntegrals. 
// The result of computation is an interval of arbitrarily
// small positive length containing the exact value
// of the product of multiple RVIntegrals.
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#ifndef MULRVINTEGRAL_H  
#define MULRVINTEGRAL_H  

#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include "PartialSum.h"
#include "RV.h"
//#include "nRV.h"
#include "Box.h"

using namespace std;
using namespace capd;
 
// MulRVIntegral class declaration
class MulRVIntegral
{
	private:

		// Required width of the interval containing the value
		// of the product of the integrals
		double precision;

		// Precision used for computing each integral
		double local_precision;

		// Coefficient determining the bounds of the integration interval
		double coef;

		// Random variables
		vector<RV> rv;

		// The interval containing the exact value of the integral
		DInterval value;

		// List of partial sums forming the value of the
		// definite integral
		vector< vector<PartialSum> > partial_sums;

		// The method performs calculation of the product of RVIntegrals.
		void calculate_value();

		// The method calculates a binomial coefficient
		//
		// @param parameters needed for calculating binomial coefficients
		double binomial_coef(int k, int n);

		// The methods performs calculation of the local precision
		// for calculating each integral in the product which guarantees
		// the correctness of the computation
		void calculate_local_error();

	public:

		// Constructor of the class
		//
		// @param vector of random variables, coefficient 
		// and precision
		MulRVIntegral(vector<RV>, double, double);

		DInterval calculate_box(Box);

		// The method returns the vector of random variables
		vector<RV> get_rv();

		// The method returns the value of the product of RVIntegrals.
		DInterval get_value();

		// The method returns precision used for calculating the 
		// product of the integrals
		double get_precision();

		// The method returns coefficient determining
		// the bounds of the integration interval in each RVIntegral
		double get_coef();

		// The method returns the precision used for calculating each
		// RVIntegral in the product
		double get_local_precision();

		// The method sets a precision used for calculating 
		// product of RVIntegrals
		//
		// @param precision
		void set_precision(double);

		// The method returns partial sums forming
		// the value of the product of RVIntegrals
		vector< vector<PartialSum> > get_partial_sums();
};
#endif 