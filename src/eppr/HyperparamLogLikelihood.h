#ifndef HYPERPARAMLOGLIKELIHOOD_H
#define HYPERPARAMLOGLIKELIHOOD_H

#include <memory>
#include <vector>
#include "ObjectiveFunction.h"
class AbstractGP;

class HyperparamLogLikelihood : public ObjectiveFunction
{
public:
	HyperparamLogLikelihood(std::shared_ptr<AbstractGP> gp, bool logspace);
	~HyperparamLogLikelihood();
private:
	std::shared_ptr<AbstractGP> gp;
	bool logspace;
public:
	double getValueAt(std::shared_ptr<std::vector<double> > point);
	std::shared_ptr<std::vector<double> > getGradientAt(std::shared_ptr<std::vector<double> > point);
};

#endif