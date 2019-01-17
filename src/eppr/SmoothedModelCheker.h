#ifndef SMOOTHEDMODELCHECKER_H
#define SMOOTHEDMODELCHECKER_H

#include <memory>
#include <vector>

class Parameter;
class ProbitRegressionPosterior;
class GpDataset;
class AnalyticApproximation;
class Parameter;
class SmmcOptions;
class GPEP;


class SmoothedModelCheker
{
public:
	SmoothedModelCheker(void);
	virtual ~SmoothedModelCheker(void);
private:
	double hyperparamOptimTimeElapsed;
	double statisticalMCTimeElapsed;
	double smoothedMCTimeElapsed;
	std::vector<double> hyperparamsUsed;
public:
	virtual double getHyperparamOptimTimeElapsed(void);
	virtual double getStatisticalMCTimeElapsed(void);
	virtual double getSmoothedMCTimeElapsed(void);
	virtual std::vector<double>& getHyperparamsUsed(void);
	virtual std::shared_ptr<GpDataset> performStatisticalModelChecking(std::vector<std::vector<double> >& x_POINTS, std::vector<double>& y_POINTS);
protected:
	std::shared_ptr<GpDataset> sp_xyPoints;
	std::shared_ptr<ProbitRegressionPosterior> sp_smoothModel;
	std::shared_ptr<AnalyticApproximation> sp_approx;
public:
	std::shared_ptr<ProbitRegressionPosterior> performSmoothedModelChecking(std::shared_ptr<GpDataset> data, std::vector<std::shared_ptr<Parameter> >& parameters, std::shared_ptr<SmmcOptions> options, std::vector<std::vector<double> >& paramValueSet);
	std::shared_ptr<AnalyticApproximation> getAnalyticApproximation(std::shared_ptr<GpDataset> data, std::vector<std::shared_ptr<Parameter> >& parameters, std::shared_ptr<SmmcOptions> options);
	void optimiseGPHyperParameters(std::shared_ptr<GPEP> gp, std::shared_ptr<SmmcOptions> options);
private:
	static double variance(std::shared_ptr<std::vector<double> > vec);
};

#endif