// nRV class extends RV class and  
// implements a normal random variable.
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#ifndef DD_H  
#define DD_H  

#include<string>
#include<vector>

using namespace std;

// nRV class declaration
class DD
{ 
	private:

		string var;
		vector<double> arg;
		vector<double> value;

	public:

		DD();

		DD(string);

		DD(string, vector<double>, vector<double>);

		string get_var();

		vector<double> get_args();

		vector<double> get_values();

		double get_arg_at(int);

		double get_value_at(int);

		void add_pair(double, double);

}; 
#endif  