// Box class implements a generic n dimensional box
// where each dimension is a partial sum of a random variable
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#include<string>
#include<sstream>
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include "Box.h"
#include "PartialSum.h"

using namespace std;
using namespace capd;

// Constructor of the class
//
// @param the dimensions of the box	
Box::Box(vector<PartialSum> dimensions)
{
	this->dimensions = dimensions;
	calculate_params();
}

Box::Box()
{
	
}

// Method for calculating parameters such as 
// box value and width of the shortest and
// the longest intervals
void Box::calculate_params()
{
	min_width = width(dimensions.at(0).get_interval());
	max_width = min_width;
	DInterval prod = dimensions.at(0).get_value();
	for(int i = 1; i < dimensions.size(); i++)
	{
		if(min_width > width(dimensions.at(i).get_interval()))
		{
			min_width = width(dimensions.at(i).get_interval());
		}
		if(max_width < width(dimensions.at(i).get_interval()))
		{
			max_width = width(dimensions.at(i).get_interval());
		} 
		prod *= dimensions.at(i).get_value();
	}
	value = prod;
}

// The method returns the dimension
// 
// @param dimension index
PartialSum Box::get_dimension(int index) const
{
	return dimensions.at(index);
}

// The method returns the box dimensions
vector<PartialSum> Box::get_dimensions()
{
	return dimensions;
}

// The methods return the box value
DInterval Box::get_value()
{
	return value;
}

void Box::set_value(DInterval value)
{
	this->value = value;
}

// The method returns the width of the shortest
// interval in the box dimensions
double Box::get_min_width()
{
	return min_width;
}

// The method returns the width of the longest
// interval in the box dimensions
double Box::get_max_width()
{
	return max_width;
}

// The method returns the value of the 
// partial some at the dimension
// 
// @param dimension index
DInterval Box::get_value_of(int index)
{
	return get_dimension(index).get_value();
}

// The method returns the interval of the
// partial some at the dimension
// 
// @param dimension index
DInterval Box::get_interval_of(int index) const
{
	return get_dimension(index).get_interval();
}

// The method returns the name of the  
// random variable at the dimension
// 
// @param dimension index
string Box::get_var_of(int index)
{
	return get_dimension(index).get_var();
}

// The method returns the name of the  
// random variable at the dimension
// 
// @param dimension index
string Box::get_fun_of(int index)
{
	return get_dimension(index).get_fun();
}

// The method returns the number of dimensions
// in the box
int Box::get_dimension_size() const
{
	return dimensions.size();
}

ostream& operator<<(ostream& strm, const Box& box)
{
	for(int i = 0; i < box.get_dimension_size() - 1; i++)
	{
		strm << box.get_interval_of(i) << "x";
	}
	strm << box.get_interval_of(box.get_dimension_size() - 1);
	
	return strm;
}

bool operator<(const Box& left, const Box& right)
{
	for(int i = 0; i < left.get_dimension_size(); i++)
	{
		if(left.get_dimension(i).get_interval().leftBound() > right.get_dimension(i).get_interval().leftBound())
		{
			return true;
		}
		if(left.get_dimension(i).get_interval().leftBound() < right.get_dimension(i).get_interval().leftBound())
		{
			return false;
		}
	}
	return false;
}

bool operator==(const Box& left, const Box& right)
{
	if(left < right) return false;
	if(right < left) return false;
	return true;
}

