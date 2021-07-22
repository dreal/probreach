#ifndef GPDATASET_H
#define GPDATASET_H

#include <vector>
#include <memory>

class KernelFunction;

class GpDataset
{
public:
	GpDataset(void);
	~GpDataset(void);
	GpDataset(int dimension);
	GpDataset(int dimension, int preemptedSize);
private:
	void init(int dimension, int preemptedSize);

	int dimension;
	std::shared_ptr<std::vector<std::vector<double> > > dataX;
	std::shared_ptr<std::vector<double> > dataY;
	std::shared_ptr<std::vector<double> > noise;
	int size;

	bool changedSinceGramCalculation;
	std::shared_ptr<KernelFunction> cachedKernel;
	std::vector<double> cachedHyperparams;
	std::shared_ptr<std::vector<std::vector<double>>> cachedGramMatrix;
public:
	void add(std::vector<std::vector<double> >& x2, std::vector<double>& y2, std::vector<double>& noise2);
	int getSize(void);
private:
	int getPreemptedSize(void);
public:
	void add(std::vector<std::vector<double> >& x2, std::vector<double>& y2);
	void add(std::vector<std::vector<double> >& x2);
	void set(std::vector<std::vector<double> >& x2);
	GpDataset(std::vector<std::vector<double> >& x);
	GpDataset(std::vector<std::vector<double> >& x, std::vector<double>& y);
	void set(std::vector<std::vector<double> >& x, std::vector<double>& y);
	std::vector<double>& getTargets(void);
private:
	std::vector<double> targets;
	std::vector<double> zeroMeanY;
	std::shared_ptr<std::vector<double> > sp_variances;
	std::shared_ptr<std::vector<std::vector<double> > > sp_dblMatrix;
public:
	int getDimension(void);
	std::shared_ptr<std::vector<std::vector<double> > >& getInstance(void);
	std::vector<double>& getInstance(int i);
	std::shared_ptr<std::vector<double> >& getNoiseTerms(void);
	double getTargetMean(void);
	std::vector<double>& getZeroMeanTargets(void);
	std::shared_ptr<std::vector<std::vector<double> > > calculateCovariances(std::shared_ptr<KernelFunction> func);
	std::shared_ptr<std::vector<std::vector<double> > > calculateCovariances(std::shared_ptr<KernelFunction> func, std::shared_ptr<GpDataset> set);
private:
	bool canUsedCachedResults(std::shared_ptr<KernelFunction> func);
	std::shared_ptr<std::vector<std::vector<double> > > allocateGramMatrix(int n);
public:
	std::shared_ptr<std::vector<double> > calculateVariances(std::shared_ptr<KernelFunction> func);
	bool isModified();
};

#endif

