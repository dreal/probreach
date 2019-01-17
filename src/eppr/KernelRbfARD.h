#ifndef KERNELRBFARD_H
#define KERNELRBFARD_H

#include <memory>
#include <vector>
#include "KernelFunction.h"


class KernelRbfARD :
	public KernelFunction
{
public:
	KernelRbfARD(int dimensions);
	KernelRbfARD(std::shared_ptr<std::vector<double> > hyp);
	virtual ~KernelRbfARD();
	virtual void setHyperarameters(std::vector<double>& hyp);
	virtual double calculate(std::vector<double>& x1, std::vector<double>& x2);
	virtual double calculateDerivative(std::vector<double>& x1, std::vector<double>& x2, int derivativeI);
	virtual double calculateSecondDerivative(std::vector<double>& x1, std::vector<double>& x2, int derivativeI, int derivativeJ);
	virtual double calculateHyperparamDerivative(std::vector<double>& x1, std::vector<double>& x2, int hyperparamIndex);
	virtual std::vector<double>& getHyperparameters(void);
	virtual std::vector<double>& getDefaultHyperarameters(std::shared_ptr<GpDataset> data);

private:
	std::shared_ptr<std::vector<double> > hyp;
	double amplitude2;
	std::shared_ptr<std::vector<double> > invLengthscale2;
	std::shared_ptr<std::vector<double> > defaultHyp;
};

#endif