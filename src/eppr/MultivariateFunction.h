#ifndef MULTIVARIATEFUNCTION_H
#define MULTIVARIATEFUNCTION_H

#include <memory>
#include <vector>

class ObjectiveFunction;

class MultivariateFunction
{
public:
	MultivariateFunction();
	~MultivariateFunction();
	virtual double value(std::shared_ptr<std::vector<double> > point);
	std::shared_ptr<ObjectiveFunction> func;
	std::shared_ptr<std::vector<double> > bestSoFar;
	std::shared_ptr<std::vector<double> > bestValueSoFar;
};

#endif

