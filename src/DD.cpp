// nRV class extends RV class and  
// implements a normal random variable.
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#include<string>
#include<iostream>
#include<vector>
#include "DD.h"
//#include "RV.h"

using namespace std;

DD::DD()
{

}

DD::DD(string var)
{
	this->var = var;
}

DD::DD(string var, vector<double> arg, vector<double> value)
{
	this->var = var;
	this->arg = arg;
	this->value = value;
}

string DD::get_var()
{
	return var;
}

vector<double> DD::get_args()
{
	return arg;
}

vector<double> DD::get_values()
{
	return value;
}

double DD::get_arg_at(int i)
{
	return arg.at(i);
}


double DD::get_value_at(int i)
{
	return value.at(i);
}

void DD::add_pair(double arg, double value)
{
	this->arg.push_back(arg);
	this->value.push_back(value);
}



