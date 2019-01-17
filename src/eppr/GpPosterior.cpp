#include "GpPosterior.h"
#include "GpDataset.h"

#include <cmath>

GpPosterior::GpPosterior(std::shared_ptr<GpDataset> inputData, std::shared_ptr<std::vector<double> > mean, std::shared_ptr<std::vector<double> > var)
{
	this->inputData = inputData;
	this->mean = mean;
	this->variance = var;
	standardDeviation = std::make_shared<std::vector<double> >(variance->size());
	for (size_t i = 0; i < standardDeviation->size(); i++)
		(*standardDeviation)[i] = sqrt((*variance)[i]);
}


GpPosterior::~GpPosterior(void)
{
}


int GpPosterior::getSize(void)
{
	return mean->size();
}


std::shared_ptr<GpDataset> GpPosterior::getInputData(void)
{
	return inputData;
}


std::shared_ptr<std::vector<double> > GpPosterior::getMean(void)
{
	return mean;
}


std::shared_ptr<std::vector<double> > GpPosterior::getVariance(void)
{
	return variance;
}


std::shared_ptr<std::vector<double> > GpPosterior::getStandardDeviation(void)
{
	return standardDeviation;
}
