// PartialSum class implements a partial sum
// used in 1/3 Simpson's rule for computing
// a definite integral of a bounded at least
// four times differentiable function.
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#ifndef PARTIALSUM_H  
#define PARTIALSUM_H  

#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>

using namespace std;
using namespace capd;

// PartialSum class declaration
class PartialSum
{ 
	private:

		// Interval where a partial sum
		// is calculated
		DInterval interval;

		// Value of the partial sum
		DInterval value;

		// Function
		string fun;

		// Name of the variable
		string var;

		// The method calculates a fourth derivative
		// of the function (fun) on the interval
		DInterval f4();

		// The method calculates the value 
		// of the partial sum
		DInterval calculate_value();

	public:

		// Constructor of the class
		//
		// @param the name of the variable, 
		// the integrated function and the interval		
		PartialSum(string, string, DInterval);

		// Constructor of the class
		//
		// @param the name of the variable, 
		// the integrated function, the interval
		// and the value of the partial sum	
		PartialSum(string, string, DInterval, DInterval);

		// The method returns the interval 
		// where the partial sum is calculated
		DInterval get_interval();

		// The method returns the value of the
		// partial sum
		DInterval get_value();

		// The methods returns the name of the
		// variable
		string get_var();

		// The method returns the function 
		string get_fun();

}; 
#endif  