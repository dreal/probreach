#include <cmath>
#include "SmoothedModelCheker.h"
#include "ProbitRegressionPosterior.h"
#include "Parameter.h"
#include "GpDataset.h"
#include "SmmcOptions.h"
#include "AnalyticApproximation.h"
#include "GPEP.h"
#include "HyperparamLogLikelihood.h"
#include "LocalOptimisation.h"
#include "PowellMethodApache.h"
#include "PointValue.h"


SmoothedModelCheker::SmoothedModelCheker(void)
{
}


SmoothedModelCheker::~SmoothedModelCheker(void)
{
}


double SmoothedModelCheker::getHyperparamOptimTimeElapsed(void)
{
	return hyperparamOptimTimeElapsed;
}


double SmoothedModelCheker::getStatisticalMCTimeElapsed(void)
{
	return statisticalMCTimeElapsed;
}


double SmoothedModelCheker::getSmoothedMCTimeElapsed(void)
{
	return smoothedMCTimeElapsed;
}


std::vector<double>& SmoothedModelCheker::getHyperparamsUsed(void)
{
	return hyperparamsUsed;
}


std::shared_ptr<GpDataset> SmoothedModelCheker::performStatisticalModelChecking(std::vector<std::vector<double> >& x_POINTS, std::vector<double>& y_POINTS)
{
	sp_xyPoints = std::make_shared<GpDataset>(x_POINTS, y_POINTS);
	return sp_xyPoints;
}

// TO DO NOT REALISED
std::shared_ptr<ProbitRegressionPosterior> SmoothedModelCheker::performSmoothedModelChecking(std::shared_ptr<GpDataset> data, std::vector<std::shared_ptr<Parameter> >& parameters, std::shared_ptr<SmmcOptions> options, std::vector<std::vector<double> >& paramValueSet)
{
	std::shared_ptr<AnalyticApproximation> approx = getAnalyticApproximation(data,
		parameters, options);

	std::shared_ptr<GpDataset> testSet = std::make_shared<GpDataset>(paramValueSet);
	sp_smoothModel = approx->getValuesAt(testSet);
	return sp_smoothModel;
}


std::shared_ptr<AnalyticApproximation> SmoothedModelCheker::getAnalyticApproximation(std::shared_ptr<GpDataset> data, std::vector<std::shared_ptr<Parameter> >& parameters, std::shared_ptr<SmmcOptions> options)
{
	std::shared_ptr<GPEP> gp = std::make_shared<GPEP>(options->getKernelGP());
	gp->setTrainingSet(data);
	gp->setScale(options->getSimulationRuns());
	gp->setCovarianceCorrection(options->getCovarianceCorrection());
//	long t0;
//	double elapsed;
	if (options->getHyperparamOptimisation()) {
		//		t0 = System.currentTimeMillis();
		optimiseGPHyperParameters(gp, options);
		//		elapsed = (System.currentTimeMillis() - t0) / 1000d;
		//		hyperparamOptimTimeElapsed = elapsed;
//		if (options->isDebugEnabled())
			//			printf("Hyperparameter optimisation: " + elapsed
			//				+ " sec");
	}

	else if (options->useDefaultHyperparams()) {
		std::vector<double>& hyp = gp->getKernel()->getDefaultHyperarameters(
			gp->getTrainingSet());
		gp->getKernel()->setHyperarameters(hyp);
	}

	hyperparamsUsed = options->getKernelGP()->getHyperparameters();
	//if (options.isDebugEnabled()) {
	//	System.out.println("amplitude:   "
	//		+ options.getKernelGP().getHypeparameters()[0]);
	//	System.out.println("lengthscale: "
	//		+ options.getKernelGP().getHypeparameters()[1]);
	//	if (options.getKernelGP() instanceof KernelRbfARD) {
	//		int dim = options.getKernelGP().getHypeparameters().length - 1;
	//		for (int i = 1; i < dim; i++)
	//			System.out.println("lengthscale: "
	//				+ options.getKernelGP().getHypeparameters()[i + 1]);
	//	}
	//}

//	resetProgress("\nProbit GP Regression...");
//	t0 = System.currentTimeMillis();
	gp->doTraining();
//	elapsed = (System.currentTimeMillis() - t0) / 1000d;
//	smoothedMCTimeElapsed = elapsed;
//	resetProgress("\n");

	//if (options.isDebugEnabled()) {
	//	System.out.println("Smoothed Model Checking:     " + elapsed
	//		+ " sec");
	//	final double lik = gp.getMarginalLikelihood();
	//	System.out.println("log-likelihood: " + lik);
	//}

	sp_approx = std::make_shared<AnalyticApproximation>(gp);
	return sp_approx;
}


void SmoothedModelCheker::optimiseGPHyperParameters(std::shared_ptr<GPEP> gp, std::shared_ptr<SmmcOptions> options)
{
	bool logspace = true;
	std::shared_ptr<HyperparamLogLikelihood> func = std::make_shared<HyperparamLogLikelihood>(gp, logspace);
	std::shared_ptr<GpDataset> train = gp->getTrainingSet();
	std::shared_ptr<std::vector<double> > init = std::make_shared<std::vector<double> >(gp->getKernel()->getDefaultHyperarameters(train));
	if (variance(std::make_shared<std::vector<double> >(train->getTargets())) == 0) {
		gp->getKernel()->setHyperarameters(*init.get());
		return; // don't bother optimising; they are all either '1' or '0'
	}

	//resetProgress("\nHyperparameter optimisation...");
	if (logspace)
		for (size_t i = 0; i < init->size(); i++)
			(*init)[i] = log((*init)[i]);

	std::shared_ptr<LocalOptimisation> alg = std::make_shared<PowellMethodApache>();
	std::shared_ptr<PointValue> best = alg->optimise(func, init);
	for (int r = 0; r < options->getHyperparamOptimisationRestarts(); r++) {
		std::shared_ptr<std::vector<double> > currentInit = std::make_shared<std::vector<double> >(init->size());
		for (size_t i = 0; i < currentInit->size(); i++)
			(*currentInit)[i] = rand() * (*init)[i] * 2.0;
		std::shared_ptr<PointValue> curr = alg->optimise(func, currentInit);
		if (curr->getValue() > best->getValue())
			best = curr;
	//	printProgress();
	}
	//resetProgress("\n");

	std::shared_ptr<std::vector<double> > point = best->getPoint();
	if (logspace)
		for (size_t i = 0; i < point->size(); i++)
			(*point)[i] = exp((*best->getPoint())[i]);
	gp->getKernel()->setHyperarameters(*point.get());

}


double SmoothedModelCheker::variance(std::shared_ptr<std::vector<double> > vec)
{
	double mean = 0.0;
	std::vector<double>::iterator v;
	for (v = vec->begin(); v != vec->end(); ++v)
		mean += (*v);
	mean = mean / (double)vec->size();
	double sum = 0.0;
	for (size_t i = 0; i < vec->size(); i++) {
		const double aux = (*vec)[i] - mean;
		sum += aux * aux;
	}
	return sum / (double)(vec->size() - 1);
}
