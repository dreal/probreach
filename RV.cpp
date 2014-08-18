#include<string>
#include<sstream>
#include "RV.h"

using namespace std;

RV::RV(string name, string var, string fun, double left, double right)
{
	this->name = name;
	this->var = var;
	this->fun = fun;
	this->left = left;
	this->right = right;
}

string RV::getName()
{
	return this->name;
}

string RV::getVar()
{
	return this->var;
}

string RV::getFun()
{
	return this->fun;
}

double RV::getLeft()
{
	return this->left;
}

double RV::getRight()
{
	return this->right;
}

string RV::toString()
{
	stringstream s;
	s << this->var << "; " << this->fun << "; " << this->left << "; " << this->right;
	return s.str();
}