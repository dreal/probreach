#include "ProbitRegressionPosterior.h"
#include <cmath>
#include "GPEP.h"


ProbitRegressionPosterior::~ProbitRegressionPosterior(void)
{
}


ProbitRegressionPosterior::ProbitRegressionPosterior(std::shared_ptr<GpDataset> inputData, std::shared_ptr<std::vector<double>> mean, std::shared_ptr<std::vector<double>> var) : GpPosterior(inputData, mean, var)
{
	cached_denominator = std::make_shared<std::vector<double> >(var->size());
	for (size_t i = 0; i < cached_denominator->size(); i++)
			(*cached_denominator)[i] = 1.0 / sqrt(1.0 + (*var)[i]);

	probabilities = std::make_shared<std::vector<double> >(mean->size());;
	for (size_t i = 0; i < probabilities->size(); i++)
		(*probabilities)[i] = standardNormalCDF((*mean)[i]);
			//	* (*cached_denominator)[i]);
}

static double invSqrt2 = 1 / sqrt(2.0);
double ProbitRegressionPosterior::standardNormalCDF(double x)
{
	return 0.5 + 0.5 * GPEP::erf(x * invSqrt2);
}


std::shared_ptr<std::vector<double> > ProbitRegressionPosterior::getClassProbabilities(void)
{
	return probabilities;
}


std::shared_ptr<std::vector<double> > ProbitRegressionPosterior::getLowerBound(double beta)
{
	std::shared_ptr<std::vector<double> > bounds = std::make_shared<std::vector<double>>(probabilities->size());
	for (size_t i = 0; i < bounds->size(); i++)
		(*bounds)[i] = standardNormalCDF(((*getMean())[i] - beta
				* (*getStandardDeviation())[i]));
				//* (*cached_denominator)[i]);
	return bounds;
}


std::shared_ptr<std::vector<double> > ProbitRegressionPosterior::getUpperBound(double beta)
{
	std::shared_ptr<std::vector<double> > bounds = std::make_shared<std::vector<double>>(probabilities->size());
	for (size_t i = 0; i < bounds->size(); i++)
		(*bounds)[i] = standardNormalCDF(((*getMean())[i] + beta
				* (*getStandardDeviation())[i]));
				//* (*cached_denominator)[i]);
	return bounds;
}
