// Box class implements a generic n dimensional box
// where each dimension is a partial sum of a random variable
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#ifndef BOX_H  
#define BOX_H 
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include "PartialSum.h"

using namespace std;
using namespace capd;

// old_Box class declaration
class old_Box
{ 
	private:

		// old_Box dimensions
		vector<PartialSum> dimensions;

		// Product of the values of the partial sums 
		// in each dimension
		DInterval value;

		// Width of the shortest interval in the box 
		// dimensions
		double min_width;

		// Width of the longest interval in the box 
		// dimensions
		double max_width;

		// Method for calculating parameters such as 
		// box value and width of the shortest and
		// the longest intervals
		void calculate_params();
  
	public:

		// Constructor of the class
		//
		// @param the dimensions of the box	
		old_Box(vector<PartialSum>);

		old_Box();

		// The method returns the box dimensions
		vector<PartialSum> get_dimensions();

		// The methods return the box value
		DInterval get_value();

		void set_value(DInterval);

		// The method returns the width of the shortest
		// interval in the box dimensions
		double get_min_width();

		// The method returns the width of the longest
		// interval in the box dimensions
		double get_max_width();

		// The method returns the dimension
		// 
		// @param dimension index
		PartialSum get_dimension(int) const;

		// The method returns the value of the 
		// partial some at the dimension
		// 
		// @param dimension index
		DInterval get_value_of(int);

		// The method returns the interval of the
		// partial some at the dimension
		// 
		// @param dimension index
		DInterval get_interval_of(int) const;

		// The method returns the name of the  
		// random variable at the dimension
		// 
		// @param dimension index
		string get_var_of(int);

		string get_fun_of(int);

		// The method returns the number of dimensions
		// in the box
		int get_dimension_size() const;

		friend ostream& operator<<(ostream&, const old_Box &);

		friend bool operator<(const old_Box &, const old_Box &);

		friend bool operator==(const old_Box &, const old_Box &);

}; 
#endif  