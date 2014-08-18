/*
 * The header file: Entry.h
 */ 
 
#ifndef ENTRY_H  
#define ENTRY_H  

#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>

using namespace std;
using namespace capd;

class Entry
{ 
	private:
		DInterval subInterval;
		DInterval partialSum;
	public:
		DInterval getSubInterval();
		DInterval getPartialSum();
		string toString();
		Entry(DInterval, DInterval);
}; 
#endif  