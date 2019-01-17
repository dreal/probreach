#ifndef GPPOSTERIOR_H
#define GPPOSTERIOR_H

#include <vector>
#include <memory>

class GpDataset;

class GpPosterior
{
public:
	GpPosterior(std::shared_ptr<GpDataset> inputData, std::shared_ptr<std::vector<double> > mean, std::shared_ptr<std::vector<double> > var);
	virtual ~GpPosterior(void);
private:
	std::shared_ptr<GpDataset> inputData;
	std::shared_ptr<std::vector<double> > mean;
	std::shared_ptr<std::vector<double> > variance;
	std::shared_ptr<std::vector<double> > standardDeviation;
public:
	int getSize(void);
	std::shared_ptr<GpDataset> getInputData(void);
	std::shared_ptr<std::vector<double> > getMean(void);
	std::shared_ptr<std::vector<double> > getVariance(void);
	std::shared_ptr<std::vector<double> > getStandardDeviation(void);
	virtual std::shared_ptr<std::vector<double> > getLowerBound(double beta) = 0;
	virtual std::shared_ptr<std::vector<double> > getUpperBound(double beta) = 0;
};

#endif