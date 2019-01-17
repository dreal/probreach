#include "AbstractGP.h"
#include "GpDataset.h"
#include "GSLAlgebra.h"

AbstractGP::AbstractGP(std::shared_ptr<KernelFunction> kernelFunction)
{
	trainingSet = std::make_shared<GpDataset>(1);
	algebra = std::make_shared<GSLAlgebra>();
	this->kernelFunction = kernelFunction;
}


AbstractGP::~AbstractGP(void)
{
}


std::shared_ptr<KernelFunction> AbstractGP::getKernel(void)
{
	return kernelFunction;
}


std::shared_ptr<GpDataset> AbstractGP::getTrainingSet(void)
{
	return trainingSet;
}


void AbstractGP::setTrainingSet(std::shared_ptr<GpDataset> trainingSet)
{
	this->trainingSet = trainingSet;
}
