#ifndef KERNELFUNCTION_H
#define KERNELFUNCTION_H

#include <memory>
#include "GpDataset.h"

class KernelFunction
{
public:
	KernelFunction(void);
	virtual ~KernelFunction(void);
	virtual double calculate(std::vector<double>& x1, std::vector<double>& x2) = 0;
	virtual double calculateDerivative(std::vector<double>& x1, std::vector<double>& x2, int derivativeI) = 0;
	virtual double calculateSecondDerivative(std::vector<double>& x1, std::vector<double>& x2, int derivativeI, int derivativeJ) = 0;
	virtual double calculateHyperparamDerivative(std::vector<double>& x1, std::vector<double>& x2, int hyperparamIndex) = 0;
	virtual std::vector<double>& getHyperparameters(void) = 0;
	virtual std::vector<double>& getDefaultHyperarameters(std::shared_ptr<GpDataset> data) = 0;
	virtual void setHyperarameters(std::vector<double>& hyp) = 0;
protected:
	std::vector<double> defaultHyp;
};

#endif