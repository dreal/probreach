// RV class implements a generic random variable.
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#ifndef RV_H  
#define RV_H 
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>

#include "PartialSum.h"

using namespace std;
using namespace capd;

// RV class declaration
class RV
{ 
	private:

		// Notation of the random variable
		string notation;

		// Name of the random variable
		string var;

		// Probability density function of the random variable
		string pdf;

		// Bounded domain of the random variable
		// (needed to perform integral computation)
		DInterval domain;

		//vector<PartialSum> partition;



	public:

		RV();

		// Class contructor
		// 
		// @param name of the random variable in a string format
		RV(string);


		RV(string, string, string, DInterval);

 		// Class destructor
 		//virtual ~RV();

		// The method returns a notation of the random variable
		// in defined form (e.g. N(0,1) for a random variable with 
		// mean = 0 and standard deviation = 1)
		string get_notation();

		// The method returns the name of the random variable
		// in a string format
		string get_var();

		// The method returns the probability density
		// function of the random variable in a string format
		string get_pdf();

		// The method returns the bounds set on the random
		// variable (needed to support integral computation)
		DInterval get_domain();

		// The method sets a notation for the defined random
		// variable
		//
		// @param notation of the random variable
		void set_notation(string);

		// The method sets a probabilty density function
		// for the defined random variable
		//
		// @param notation of the random variable
		void set_pdf(string);

		// The method sets a bounded domain for the defined
		// random variable (in order to support the integral
		// computation)
		//
		// @param bounded domain of the random variable
		void set_domain(DInterval);
}; 
#endif  