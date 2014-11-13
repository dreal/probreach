// BoxFactory class implements static methods for manipulating Boxes
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#ifndef BOXFACTORY_H  
#define BOXFACTORY_H 
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include "PartialSum.h"
#include "Box.h"

using namespace std;
using namespace capd;

// BoxFactory class declaration
class BoxFactory
{ 
	private:
		
	public:

		// The method gets a vector of vectors of PartialSum as an input parameter
		// and return a Cartesian product of the vectors
		static vector<Box> calculate_cart_prod(vector< vector<PartialSum> >);

		// The method gets a Box of n demensions as an input parameter and returns 
		// a vector of 2^n boxes obtained by dividing each edge of the primary 
		// box in halves
		static vector<Box> branch_box(Box);
		
}; 
#endif  