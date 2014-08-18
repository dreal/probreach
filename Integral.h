/**
 * Integral class declaration
 */
 
#ifndef INTEGRAL_H  
#define INTEGRAL_H  

#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include "Entry.h"

using namespace std;
using namespace capd;
 
class Integral
{
	private:
		double precision;
		double a;
		double b;
		DInterval I;
		IFunction f;
		IMap _f;
		vector<Entry> entries;
		vector<DInterval> intervals;
		
	public:
		Integral();
		Integral(string, string, double, double, double);
		void setFunctionFromString(string, string);
		IFunction getFunction();
		void setFunction(IFunction);
		IMap getMap();
		void setMap(IMap);
		double getPrecision();
		void setPrecision(double);
		DInterval solve();
		vector<Entry> getEntries();
		vector<DInterval> getIntervals();
		DInterval f4(DInterval);
		DInterval calculateS(DInterval);
};
#endif 