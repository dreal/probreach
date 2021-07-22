#ifndef KERNELRBF_H
#define KERNELRBF_H

#include "KernelFunction.h"
class KernelRBF :
	public KernelFunction
{
public:
	KernelRBF(void);
	virtual ~KernelRBF(void);
	virtual double calculate(std::vector<double>& x1, std::vector<double>& x2);
	virtual double calculateDerivative(std::vector<double>& x1, std::vector<double>& x2, int derivativeI);
	virtual double calculateSecondDerivative(std::vector<double>& x1, std::vector<double>& x2, int derivativeI, int derivativeJ);
	virtual double calculateHyperparamDerivative(std::vector<double>& x1, std::vector<double>& x2, int hyperparamIndex);
	virtual std::vector<double>& getHyperparameters(void);
	virtual std::vector<double>& getDefaultHyperarameters(std::shared_ptr<GpDataset> data);
	virtual void setHyperarameters(std::vector<double>& hyp);
private:
    std::vector<double> hyp;
	double amplitude2;
	double invLengthscale2;
public:
	KernelRBF(double a, double l);
};

#endif
