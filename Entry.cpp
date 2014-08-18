#include "Entry.h"
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<iomanip>
#include<string>

using namespace std;
using namespace capd;

Entry::Entry(DInterval subInterval, DInterval partialSum)
{
	this->subInterval = subInterval;
	this->partialSum = partialSum;
}

DInterval Entry::getSubInterval()
{
	return this->subInterval;
}

DInterval Entry::getPartialSum()
{
	return this->partialSum;
}

string Entry::toString()
{
	
	stringstream s;
	s << setprecision(16) << "I(" << this->subInterval << ") = " << this->partialSum;
	return s.str();
	
}