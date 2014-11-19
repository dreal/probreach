// BoxFactory class implements static methods for manipulating Boxes
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#include<string>
#include<sstream>
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include "BoxFactory.h"
#include "Box.h"
#include "PartialSum.h"

using namespace std;
using namespace capd;

// The method gets a vector of vectors of PartialSum as an input parameter
// and return a Cartesian product of the vectors
vector<Box> BoxFactory::calculate_cart_prod(vector< vector<PartialSum> > partial_sums)
{
	int elem = 1;
	vector<Box> cart_prod;
	for(int i = 0; i < partial_sums.size(); i++) elem *= partial_sums.at(i).size();
	
	for(int i = 0; i < elem; i++)
	{
		int index = i;
		vector<PartialSum> tmp_vector;
		for(int j = 0; j < partial_sums.size(); j++)
		{
			int mult = 1;
			for(int k = partial_sums.size() - 1; k > j; k--)
			{
				mult *= partial_sums.at(k).size();
			}
			int tmp_index = index / mult;
			tmp_vector.push_back(partial_sums.at(j).at(tmp_index));
			index -= tmp_index * mult;
		}
		cart_prod.push_back(Box(tmp_vector));
	}
	return cart_prod;
}

// The method gets a Box of n demensions as an input parameter and returns 
// a vector of 2^n boxes obtained by dividing each edge of the primary 
// box in halves
vector<Box> BoxFactory::branch_box(Box box)
{
	vector<PartialSum> dimensions = box.get_dimensions();
	vector <vector<PartialSum> > partial_sums;
	for(int i = 0; i < dimensions.size(); i++)
	{
		vector<PartialSum> tmp;
		DInterval left_interval(dimensions.at(i).get_interval().leftBound(), dimensions.at(i).get_interval().mid().rightBound());
		DInterval right_interval(dimensions.at(i).get_interval().mid().leftBound(), dimensions.at(i).get_interval().rightBound());
		tmp.push_back(PartialSum(dimensions.at(i).get_var(), dimensions.at(i).get_fun(), left_interval));
		tmp.push_back(PartialSum(dimensions.at(i).get_var(), dimensions.at(i).get_fun(), right_interval));
		partial_sums.push_back(tmp);
	}
	return BoxFactory::calculate_cart_prod(partial_sums);
}

bool BoxFactory::compare_boxes_des(Box left, Box right)
{
	return (left.get_value().leftBound() > right.get_value().leftBound());
}
