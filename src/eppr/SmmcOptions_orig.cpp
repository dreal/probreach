#include "SmmcOptions.h"
#include "RegularSampler.h"
#include "KernelRBF.h"
#include "KernelRbfARD.h"

SmmcOptions::SmmcOptions(int dimensions_hyp)
{
	simulationEndTime = 0;
	simulationRuns = 20;
	simulationTimepoints = 200;
	timeseriesEnabled = true;

	initialObservtions = 20;
	numberOfTestPoints = 100;
	testpoints = nullptr;
	sampler = std::make_shared<RegularSampler>();

	std::shared_ptr<std::vector<double> > hyp = std::make_shared<std::vector<double> >();
	for (int i = 0; i < dimensions_hyp; i++) {
		hyp->push_back(1.0);
	}

	kernelGP = std::make_shared<KernelRbfARD>(hyp);
	_useDefaultHyperparams = true;
	hyperparamOptimisation = true;
	hyperparamOptimisationRestarts = 0;
	covarianceCorrection = 1e-4;

	debugEnabled = false;
}


SmmcOptions::~SmmcOptions(void)
{
}


SmmcOptions::SmmcOptions(const SmmcOptions& copy)
{
	this->simulationEndTime = copy.simulationEndTime;
	this->simulationRuns = copy.simulationRuns;
	this->simulationTimepoints = copy.simulationTimepoints;
	this->timeseriesEnabled = copy.timeseriesEnabled;
	this->initialObservtions = copy.initialObservtions;
	this->numberOfTestPoints = copy.numberOfTestPoints;
	this->sampler = copy.sampler;
	this->kernelGP = copy.kernelGP;
	this->hyperparamOptimisation = copy.hyperparamOptimisation;
	this->hyperparamOptimisationRestarts = copy.hyperparamOptimisationRestarts;
	this->covarianceCorrection = copy.covarianceCorrection;
	this->debugEnabled = copy.debugEnabled;
}


bool SmmcOptions::isDebugEnabled(void)
{
	return debugEnabled;
}


double SmmcOptions::getSimulationEndTime(void)
{
	return simulationEndTime;
}


void SmmcOptions::setSimulationEndTime(double simulationEndTime)
{
	this->simulationEndTime = simulationEndTime;
}


int SmmcOptions::getN(void)
{
	return initialObservtions;
}


void SmmcOptions::setN(int datapoints)
{
	this->initialObservtions = datapoints;
}


int SmmcOptions::getNumberOfTestPoints(void)
{
	return numberOfTestPoints;
}


void SmmcOptions::setNumberOfTestPoints(int datapoints)
{
		this->numberOfTestPoints = datapoints;
		testpoints = nullptr;
}


std::shared_ptr<std::vector<std::vector<double> > >& SmmcOptions::getTestpoints(void)
{
	return testpoints;
}


void SmmcOptions::setTestpoints(std::shared_ptr<std::vector<std::vector<double> > > testpoints)
{
	this->testpoints = testpoints;
}


int SmmcOptions::getSimulationRuns(void)
{
	return simulationRuns;
}


int SmmcOptions::getSimulationTimepoints(void)
{
	return simulationTimepoints;
}


bool SmmcOptions::isTimeseriesEnabled(void)
{
	return timeseriesEnabled;
}


std::shared_ptr<KernelFunction>& SmmcOptions::getKernelGP(void)
{
	return kernelGP;
}


bool SmmcOptions::useDefaultHyperparams(void)
{
	return _useDefaultHyperparams;
}



void SmmcOptions::setUseDefaultHyperparams(bool useDefaultHyperparams)
{
	this->_useDefaultHyperparams = useDefaultHyperparams;
}


bool SmmcOptions::getHyperparamOptimisation(void)
{
	return hyperparamOptimisation;
}



int SmmcOptions::getHyperparamOptimisationRestarts(void)
{
	return hyperparamOptimisationRestarts;
}


double SmmcOptions::getCovarianceCorrection(void)
{
	return covarianceCorrection;
}


void SmmcOptions::setDebugEnabled(bool debugEnabled)
{
	this->debugEnabled = debugEnabled;
}


void SmmcOptions::setSimulationRuns(int simulationRuns)
{
	this->simulationRuns = simulationRuns;
}



void SmmcOptions::setSimulationTimepoints(int simulationTimepoints)
{
	this->simulationTimepoints = simulationTimepoints;
}


void SmmcOptions::setTimeseriesEnabled(bool timeseriesEnabled)
{
	this->timeseriesEnabled = timeseriesEnabled;
}


std::shared_ptr<GridSampler>& SmmcOptions::getSampler(void)
{
	return sampler;
}


void SmmcOptions::setSampler(std::shared_ptr<GridSampler> sampler)
{
	this->sampler = sampler;
}


void SmmcOptions::setKernelGP(std::shared_ptr<KernelFunction> kernelGP)
{
	this->kernelGP = kernelGP;
}


void SmmcOptions::setHyperparamOptimisation(bool hyperparamOptimisation)
{
	this->hyperparamOptimisation = hyperparamOptimisation;
}


void SmmcOptions::setHyperparamOptimisationRestarts(int hyperparamOptimisationRestarts)
{
	this->hyperparamOptimisationRestarts = hyperparamOptimisationRestarts;
}


void SmmcOptions::setCovarianceCorrection(double covarianceCorrection)
{
	this->covarianceCorrection = covarianceCorrection;
}
