#ifndef OBJECTIVEFUNCTION_H
#define OBJECTIVEFUNCTION_H

#include <memory>
#include <vector>

class ObjectiveFunction
{
public:
	ObjectiveFunction();
	virtual ~ObjectiveFunction();
	virtual double getValueAt(std::shared_ptr<std::vector<double> > point) = 0;
};

#endif