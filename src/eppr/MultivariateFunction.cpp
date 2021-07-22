#include "MultivariateFunction.h"
#include "ObjectiveFunction.h"
#include <limits>

MultivariateFunction::MultivariateFunction()
{
	bestSoFar = nullptr;
	func = nullptr;
	bestValueSoFar = std::make_shared<std::vector<double> >(1);
	(*bestValueSoFar)[0] = -std::numeric_limits<double>::max(); 
}


MultivariateFunction::~MultivariateFunction()
{
}


double MultivariateFunction::value(std::shared_ptr<std::vector<double> > point)
{
	const double value = func->getValueAt(point);
	if (value > (*bestValueSoFar)[0]) {
		(*bestValueSoFar)[0] = value;
		std::copy(point->begin(), point->end(), bestSoFar->begin());
	}
	return value;
}
