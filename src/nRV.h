// nRV class extends RV class and  
// implements a normal random variable.
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#ifndef nRV_H  
#define nRV_H  

#include<string>
#include "RV.h"

using namespace std;

// nRV class declaration
class nRV: public RV
{ 
	private:

		// The mean of the normal random variable
		double mean;

		// Standrad deviation of the normal random variable
		double deviation;

		// The method generates a notation
		// of the form N(mean, deviation)
		string generate_notation();

		// The method generates an probability 
		// density function in a string format
		string generate_pdf(string);

	public:

		// Class contructor
		// 
		// @param name of the random variable in a string format, 
		// mean and standard deviation
		nRV(string, double, double);

		// The method returns the value of the mean
		double get_mean();

		// The method returns the value of the standard deviation
		double get_deviation();
}; 
#endif  