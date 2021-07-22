#ifndef SMMCOPTONS_H
#define SMMCOPTONS_H

#include <memory>
#include "KernelFunction.h"
#include "GridSampler.h"

class SmmcOptions
{
public:
	SmmcOptions(int dimensions_hyp);
	~SmmcOptions(void);
private:
	double simulationEndTime;
	int simulationRuns;
	int simulationTimepoints;
	bool timeseriesEnabled;

	int initialObservtions;
	int numberOfTestPoints;
	std::shared_ptr<std::vector<std::vector<double>>> testpoints;
	std::shared_ptr<GridSampler> sampler;

	std::shared_ptr<KernelFunction> kernelGP;
	bool _useDefaultHyperparams;
	bool hyperparamOptimisation;
	int hyperparamOptimisationRestarts;
	double covarianceCorrection;

	bool debugEnabled;
public:
	SmmcOptions(const SmmcOptions& copy);
	bool isDebugEnabled(void);
	double getSimulationEndTime(void);
	void setSimulationEndTime(double simulationEndTime);
	int getN(void);
	void setN(int datapoints);
	int getNumberOfTestPoints(void);
	void setNumberOfTestPoints(int datapoints);
	std::shared_ptr<std::vector<std::vector<double> > >& getTestpoints(void);
	void setTestpoints(std::shared_ptr<std::vector<std::vector<double> > > testpoints);
	int getSimulationRuns(void);
	int getSimulationTimepoints(void);
	bool isTimeseriesEnabled(void);
	std::shared_ptr<KernelFunction>& getKernelGP(void);
	bool useDefaultHyperparams(void);
	void setUseDefaultHyperparams(bool useDefaultHyperparams);
	bool getHyperparamOptimisation(void);
	int getHyperparamOptimisationRestarts(void);
	double getCovarianceCorrection(void);
	void setDebugEnabled(bool debugEnabled);
	void setSimulationRuns(int simulationRuns);
	void setSimulationTimepoints(int simulationTimepoints);
	void setTimeseriesEnabled(bool timeseriesEnabled);
	std::shared_ptr<GridSampler>& getSampler(void);
	void setSampler(std::shared_ptr<GridSampler> sampler);
	void setKernelGP(std::shared_ptr<KernelFunction> kernelGP);
	void setHyperparamOptimisation(bool hyperparamOptimisation);
	void setHyperparamOptimisationRestarts(int hyperparamOptimisationRestarts);
	void setCovarianceCorrection(double covarianceCorrection);
};

#endif