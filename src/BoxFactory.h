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
#include "old_Box.h"

using namespace std;
using namespace capd;

// BoxFactory class declaration
class BoxFactory
{ 
	private:
		
	public:

		// The method gets a vector of vectors of PartialSum as an input parameter
		// and return a Cartesian product of the vectors
		static vector<old_Box> calculate_cart_prod(vector< vector<PartialSum> >);

		// The method gets a old_Box of n demensions as an input parameter and returns
		// a vector of 2^n boxes obtained by dividing each edge of the primary 
		// box in halves
		static vector<old_Box> branch_box(old_Box);

		static vector<old_Box> branch_box(old_Box, std::map<string, double>);

		static bool compare_boxes_des(old_Box, old_Box);

		static vector<old_Box> merge_boxes(vector<old_Box>);

		static old_Box merge_two_boxes(old_Box, old_Box);

		static int compare_boxes(old_Box, old_Box);

		static vector<old_Box> cut_box(old_Box, old_Box);

		//static old_Box two_boxes_intersection(old_Box, old_Box);

		//static old_Box boxes_intersection(vector<old_Box>);

		//static vector<old_Box> vectors_intersection(vector<old_Box>, vector<old_Box>);
		
}; 
#endif  