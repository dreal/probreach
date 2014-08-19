/**
 * Class for manipulating Entries.
 * Contains the interval of the random variable and the interval containing a value of the partial sum on this interval
 *
 * @author: Fedor Shmarov
 * @e-mail: f.shmarov@ncl.ac.uk
 */
#include "Entry.h"
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<iomanip>
#include<string>

using namespace std;
using namespace capd;

/**
 * Constructor
 *
 * @param subInterval is the interval where the random variable is defined and
 * partialSum is an interval containin the value of the partial sum on the defined interval
 *
 */
Entry::Entry(DInterval subInterval, DInterval partialSum)
{
	this->subInterval = subInterval;
	this->partialSum = partialSum;
}

/**
 * Returns interval
 *
 * @return interval
 */
DInterval Entry::getSubInterval()
{
	return this->subInterval;
}

/**
 * Returns the interval containing the value of the partial sum
 *
 * @return partial sum
 */
DInterval Entry::getPartialSum()
{
	return this->partialSum;
}

/**
 * Returns string representation of Entry
 *
 * @return string representation of Entry
 */
string Entry::toString()
{
	
	stringstream s;
	s << setprecision(16) << "I(" << this->subInterval << ") = " << this->partialSum;
	return s.str();
	
}