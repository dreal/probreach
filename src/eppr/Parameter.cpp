#include "Parameter.h"


Parameter::Parameter(void)
{
}


Parameter::~Parameter(void)
{
}


Parameter::Parameter(std::string name, double lBound, double uBound) 
{
	this->name = name;
	this->lowerBound = lBound;
	this->upperBound = uBound;
	if (lBound >= uBound)
		throw ("lBound >= uBound");
}


std::string& Parameter::getName(void)
{
	return name;
}


double Parameter::getLowerBound(void)
{
	return lowerBound;
}


double Parameter::getUpperBound(void)
{
	return upperBound;
}
