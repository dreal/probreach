/**
 * Class containing methods for calculating the interval of an arbitrary positive length
 * containing the exact value of the integral of the continuous function on the interval
 *
 * @author: Fedor Shmarov
 * @e-mail: f.shmarov@ncl.ac.uk
 */
#include "Integral.h"
#include "Entry.h"
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<iomanip>
#include<string>

/**
 * Default constructor
 */
Integral::Integral()
{
}

/**
 * Constructor
 */
Integral::Integral(string var, string funString, double a, double b, double precision)
{
	this->I = DInterval(0.0);
	this->a = a;
	this->b = b;
	this->f = IFunction("var:" + var + ";fun:" + funString + ";");
	this->_f = IMap("var:" + var + ";fun:" + funString + ";");
	this->_f.setDegree(4);
	this->precision = precision;
	this->intervals.push_back(DInterval(a, (b + a) / 2));
	this->intervals.push_back(DInterval((b + a) / 2, b));
}

/**
 * Getters and setters
 */
double Integral::getPrecision()
{
	return precision;
}

void Integral::setPrecision(double precision)
{
	this->precision = precision;
}

IFunction Integral::getFunction()
{
	return f;
}

void Integral::setFunction(IFunction f)
{
	this->f = f;
}

IMap Integral::getMap()
{
	return _f;
}

void Integral::setMap(IMap _f)
{
	this->_f = _f;
}

void Integral::setFunctionFromString(string var, string funString)
{
	this->f = IFunction("var:" + var + ";fun:" + funString + ";");
	this->_f = IMap("var:" + var + ";fun:" + funString + ";");
	this->_f.setDegree(4);
}

vector<Entry> Integral::getEntries()
{
	return this->entries;
}

vector<DInterval> Integral::getIntervals()
{
	return this->intervals;
}

/**
 * Calculating the interval enclosing the value of the fourth derivative of the function on the interval
 *
 * @param v interval on which the value of the fourth derivatives should be found
 *
 * @returm fourth derivative of the function on the interval
 */
DInterval Integral::f4(DInterval v)
{
	DInterval vArray[] = {v};
  	IVector x(1,vArray);

	IJet jet(1,1,4);
	_f(x,jet);

	//multiply by 24 because jet(0, 3) is the value of the fourth Taylor coefficient = (f4) / 4!)
	return jet(0, 3) * 24;
}

/**
 * Calculating the interval enclosing the value of the partial sum of the function on the interval
 *
 * @param x interval on which the value of the partial sum should be found
 *
 * @returm partial sum of the function on the interval x
 */
DInterval Integral::calculateS(DInterval x)
{
	return (width(x) / 6) * (f(x.leftBound()) + 4 * f(x.mid()) + f(x.rightBound())) - (width(x) * width(x) * width(x) * width(x) * width(x) / 2880) * f4(x);
}

/**
 * Calculating the interval enclosing the value of the intergal
 *
 * @returm interval containing the value of the integral
 */
DInterval Integral::solve()
{
	while (intervals.size() > 0)
	{
				
		DInterval x = intervals.front();
		intervals.erase(intervals.begin());
		
		DInterval S = calculateS(x);
	
		if (width(S) > precision * (width(x) / (b - a)))
		{
			intervals.push_back(DInterval(x.leftBound(), x.mid().rightBound()));
			intervals.push_back(DInterval(x.mid().leftBound(), x.rightBound()));
		}
		else
		{
			entries.push_back(Entry(x, S));
			I += S;
		}

	}

	return I;
}
