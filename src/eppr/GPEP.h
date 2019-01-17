#ifndef GPEP_H
#define GPEP_H

#include <memory>
#include <vector>
#include "AbstractGP.h"

class GpDataset;
class IAlgebra;
class IMatrix;
class KernelFunction;
class GpPosterior;
class Gauss;
class CavGauss;
class EPupdate;
class ProbitRegressionPosterior;

class GPEP : public AbstractGP
{
public:
	GPEP(std::shared_ptr<KernelFunction> kernel);
	virtual ~GPEP();
	static double erf(double x);
	static double CORRECTION_FACTOR;
public:
	//virtual std::shared_ptr<KernelFunction> getKernel(void);
	//virtual std::shared_ptr<GpDataset> getTrainingSet(void);
	//virtual void setTrainingSet(std::shared_ptr<GpDataset> trainingSet);
private:
	double eps_damp;
	int scale;
	double covarianceCorrection;
	std::shared_ptr<IMatrix> invC;
	std::shared_ptr<IMatrix> mu_tilde;
	double logdet_LC;
	const static double sqrt2;
	const static double invSqrt2;
	const static double log_2;
public:
	virtual void setScale(int scale);
	virtual int getScale(void);
	void setCovarianceCorrection(double covarianceCorrection);
	void doTraining(void);
	std::shared_ptr<Gauss> expectationPropagation(double tolerance);
private:
	double computeMarginalMoments(std::shared_ptr<Gauss> gauss, std::shared_ptr<IMatrix> Term);
	void gausshermite(int n, std::shared_ptr<IMatrix> x, std::shared_ptr<IMatrix> w);
	std::shared_ptr<CavGauss> ComputeCavities(std::shared_ptr<Gauss> gauss, std::shared_ptr<IMatrix> Term);
	std::shared_ptr<EPupdate> ep_update(std::shared_ptr<CavGauss> cavGauss, std::shared_ptr<IMatrix> Term, double eps_damp, void* LogLikFunc , std::shared_ptr<IMatrix> LikPar_p, std::shared_ptr<IMatrix> LikPar_q, std::shared_ptr<IMatrix> xGauss, std::shared_ptr<IMatrix> wGauss);
	std::shared_ptr<IMatrix> GaussHermiteNQ(std::shared_ptr<IMatrix> FuncPar_p, std::shared_ptr<IMatrix> FuncPar_q, std::shared_ptr<IMatrix> m, std::shared_ptr<IMatrix> v, std::shared_ptr<IMatrix> xGH, std::shared_ptr<IMatrix> logwGH, std::shared_ptr<IMatrix> Cumul);
	std::shared_ptr<IMatrix> logprobitpow(std::shared_ptr<IMatrix> X, std::shared_ptr<IMatrix> LikPar_p, std::shared_ptr<IMatrix> LikPar_q);
	static double ncdflogbc(double x);
public:
	std::shared_ptr<ProbitRegressionPosterior> getGpPosterior(std::shared_ptr<GpDataset> testSet);
private:
	std::shared_ptr<ProbitRegressionPosterior> sp_posterior;
	std::shared_ptr<std::vector<double> > sp_data1;
	std::shared_ptr<std::vector<double> > sp_data2;
	std::shared_ptr<Gauss> gauss;

public:
	double getMarginalLikelihood();
	std::shared_ptr<std::vector<double> > getMarginalLikelihoodGradient();
};

#endif