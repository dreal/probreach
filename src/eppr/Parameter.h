#ifndef PARAMETER_H
#define PARAMETER_H

#include <string>

class Parameter
{
public:
	Parameter(void);
	~Parameter(void);
private:
	std::string name;
	double lowerBound;
	double upperBound;
public:
	Parameter (std::string name, double lBound, double uBound);
	std::string& getName(void);
	double getLowerBound(void);
	double getUpperBound(void);
};

#endif