#ifndef PROBITREGRESSIONPOSTERIOR_H
#define PROBITREGRESSIONPOSTERIOR_H

#include <vector>
#include <memory>
#include "GpDataset.h"
#include "GpPosterior.h"

class ProbitRegressionPosterior : public GpPosterior
{
public:
	ProbitRegressionPosterior(std::shared_ptr<GpDataset> inputData, std::shared_ptr<std::vector<double> > mean, std::shared_ptr<std::vector<double> > var);
	virtual ~ProbitRegressionPosterior(void);
private:

	std::shared_ptr<std::vector<double> > probabilities;
	std::shared_ptr<std::vector<double> > cached_denominator;
public:
	static double standardNormalCDF(double x);
	std::shared_ptr<std::vector<double> > getClassProbabilities(void);
	virtual std::shared_ptr<std::vector<double> > getLowerBound(double beta);
	virtual std::shared_ptr<std::vector<double> > getUpperBound(double beta);
};

#endif