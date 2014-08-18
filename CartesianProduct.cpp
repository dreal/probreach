#include<iostream>
#include<string>
#include<iomanip>
#include<fstream>
#include<math.h>
#include<gsl/gsl_cdf.h>
#include<gsl/gsl_rng.h>
#include "CartesianProduct.h"
#include "Entry.h"

using namespace std;

//template <typename Type>
vector< vector<Entry> > cartesianProduct(vector< vector<Entry> > input)
{
	vector< vector<Entry> > output;
	
	int elem = 1;
	for(int i = 0; i < input.size(); i++) elem *= input.at(i).size();
	
	for(int i = 0; i < elem; i++)
	{
		int index = i;
		vector<Entry> tmp_vector;
		for(int j = 0; j < input.size(); j++)
		{
			int mult = 1;
			for(int k = input.size() - 1; k > j; k--)
			{
				mult *= input.at(k).size();
			}
		
			int tmp_index = index / mult;
			tmp_vector.push_back(input.at(j).at(tmp_index));
			index -= tmp_index * mult;
		}
		output.push_back(tmp_vector);
	}

	return output;
}






