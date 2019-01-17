#ifndef ABSTRACTGP_H
#define ABSTRACTGP_H

#include <vector>
#include <memory>

class IAlgebra;
class KernelFunction;

class ProbitRegressionPosterior;
class GpDataset;
class ProbitRegressionPosterior;

class AbstractGP
{
public:
	AbstractGP(std::shared_ptr<KernelFunction> kernelFunction);
	virtual ~AbstractGP(void);
	virtual std::shared_ptr<ProbitRegressionPosterior> getGpPosterior(std::shared_ptr<GpDataset> testSet) = 0;
	virtual double getMarginalLikelihood() = 0;
	virtual std::shared_ptr<std::vector<double> > getMarginalLikelihoodGradient() = 0;
protected:
	std::shared_ptr<IAlgebra> algebra;
	std::shared_ptr<KernelFunction> kernelFunction;
	std::shared_ptr<GpDataset> trainingSet;
public:
	virtual std::shared_ptr<KernelFunction> getKernel(void);
	virtual std::shared_ptr<GpDataset> getTrainingSet(void);
	virtual void setTrainingSet(std::shared_ptr<GpDataset> trainingSet);
};

#endif