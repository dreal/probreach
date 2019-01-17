#ifndef LOCALOPTIMISATION_H
#define LOCALOPTIMISATION_H

#include <memory>
#include <vector>

class PointValue;
class ObjectiveFunction;

class LocalOptimisation
{
public:
	LocalOptimisation();
	virtual ~LocalOptimisation();
	virtual std::shared_ptr<PointValue> optimise(std::shared_ptr<ObjectiveFunction> func,
		std::shared_ptr<std::vector<double> > init) = 0;
};

#endif

