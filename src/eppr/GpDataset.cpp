#include "GpDataset.h"
#include "KernelFunction.h"

GpDataset::GpDataset(void)
{

}


GpDataset::~GpDataset(void)
{
}


GpDataset::GpDataset(int dimension) 
{
	init(dimension, 0);
}


GpDataset::GpDataset(int dimension, int preemptedSize)
{
	init(dimension, preemptedSize);
}


void GpDataset::init(int dimension, int preemptedSize)
{
	size = 0;
	changedSinceGramCalculation = true;
	cachedKernel = nullptr;
	cachedHyperparams.clear();
	cachedGramMatrix = nullptr;
	//cachedGramMatrix->clear();

	this->dimension = dimension;
	std::shared_ptr<std::vector<std::vector<double> > > x(new std::vector<std::vector<double> >(preemptedSize));
	for(int i = 0; i < preemptedSize; ++i) (*x)[i].resize(dimension);
	dataX = x;
	
	dataY = std::make_shared<std::vector<double>>(preemptedSize);
	noise = std::make_shared<std::vector<double>>(preemptedSize);
}


void GpDataset::add(std::vector<std::vector<double> >& x2, std::vector<double>& y2, std::vector<double>& noise2)
{
		if (x2.size() != y2.size() || x2.size() != noise2.size())
			throw "IllegalArgumentException";

		const int size1 = getSize();
		const int size2 = x2.size();
		const int size12 = size1 + size2;
		if (size12 > getPreemptedSize()) {
			std::shared_ptr<std::vector<std::vector<double> > > x12(new std::vector<std::vector<double> >(size12));
			for(int i = 0; i < size12; ++i) (*x12)[i].resize(dimension);
			std::shared_ptr<std::vector<double> > y12(new std::vector<double>(size12));
			std::shared_ptr<std::vector<double> > noise12(new std::vector<double>(size12));
			for (int i = 0; i < size1; i++)
				std::copy((*dataX)[i].begin(), (*dataX)[i].end(), (*x12)[i].begin());
			std::copy(dataY->begin(), dataY->end(), y12->begin());
			std::copy(noise->begin(), noise->end(), noise12->begin());
			dataX = x12;
			dataY = y12;
			noise = noise12;
		}
		for (int i = size1; i < size12; i++) {
			std::copy(x2[i - size1].begin(), x2[i - size1].end(), (*dataX)[i].begin());
		}
		std::copy(y2.begin(), y2.end(), dataY->begin());
		std::copy(noise2.begin(), noise2.end(), noise->begin());
		size = size12;
		changedSinceGramCalculation = true;
}


int GpDataset::getSize(void)
{
	return size;
}


int GpDataset::getPreemptedSize(void)
{
	if (dataX == nullptr) throw "dataX is NULL";
	return dataX->size();
}


void GpDataset::add(std::vector<std::vector<double> >& x2, std::vector<double>& y2)
{
	std::vector<double> noise(x2.size());
	add(x2, y2, noise);
}


void GpDataset::add(std::vector<std::vector<double> >& x2)
{
	std::vector<double> y(x2.size());
	add(x2, y);
}


void GpDataset::set(std::vector<std::vector<double> >& x)
{
	size = 0;
	add(x);
}


GpDataset::GpDataset(std::vector<std::vector<double> >& x)
{
	init(x[0].size(), x.size());
	set(x);
}


GpDataset::GpDataset(std::vector<std::vector<double> >& x, std::vector<double>& y)
{
	init(x[0].size(), x.size());
	set(x,y);
}


void GpDataset::set(std::vector<std::vector<double> >& x, std::vector<double>& y)
{
	size = 0;
	add(x, y);
}


std::vector<double>& GpDataset::getTargets(void)
{
	targets.resize(getSize());
	std::copy(dataY->begin(), dataY->end(), targets.begin());
	return targets;
}


int GpDataset::getDimension(void)
{
	return dimension;
}


std::shared_ptr<std::vector<std::vector<double> > >& GpDataset::getInstance(void)
{
	return dataX;
}

std::vector<double>& GpDataset::getInstance(int i) {
	return (*dataX)[i];
}

std::shared_ptr<std::vector<double> >& GpDataset::getNoiseTerms(void)
{
	return noise;
}


double GpDataset::getTargetMean(void)
{
	double sum = 0;
	for (int i = 0; i < getSize(); i++)
		sum += (*dataY)[i];
	return sum / getSize();
}


std::vector<double>& GpDataset::getZeroMeanTargets(void)
{
	const double meanY = getTargetMean();
	zeroMeanY.resize(getSize());
	std::copy(dataY->begin(), dataY->end(), zeroMeanY.begin());
	for (int i = 0; i < getSize(); i++)
		zeroMeanY[i] -= meanY;
	return zeroMeanY;
}


std::shared_ptr<std::vector<std::vector<double> > > GpDataset::calculateCovariances(std::shared_ptr<KernelFunction> func)
{
		if (canUsedCachedResults(func))
			changedSinceGramCalculation = false;
		else
			changedSinceGramCalculation = true;

		std::shared_ptr<std::vector<std::vector<double> > >  x = this->dataX;
		const int n = this->getSize();
		std::shared_ptr<std::vector<std::vector<double> > > result = allocateGramMatrix(n);

		if (canUsedCachedResults(func)) {
			const int m = cachedGramMatrix->size();
			for (int i = 0; i < n; i++) {
				if (i < m)
					(*result)[i][i] = (*cachedGramMatrix)[i][i];
				else
					(*result)[i][i] = func->calculate((*x)[i], (*x)[i]);
				for (int j = i + 1; j < n; j++)
					if (i < m && j < m)
						(*result)[j][i] = (*result)[i][j] = (*cachedGramMatrix)[i][j];
					else
						(*result)[j][i] = (*result)[i][j] = func->
								calculate((*x)[i], (*x)[j]);
			}
		}

		else
			for (int i = 0; i < n; i++) {
				(*result)[i][i] = func->calculate((*x)[i], (*x)[i]);
				for (int j = i + 1; j < n; j++)
					(*result)[j][i] = (*result)[i][j] = func->calculate((*x)[i], (*x)[j]);
			}

		cachedGramMatrix = result;
		//cachedKernel = func.getClass();
		cachedHyperparams = func->getHyperparameters();
		//cachedHyperparams = Arrays.copyOf(cachedHyperparams,
		//		cachedHyperparams.length);
		return result;
	
}

bool GpDataset::canUsedCachedResults(std::shared_ptr<KernelFunction> func)
{
	//cachedHyperparams
	bool equal = true;
	std::vector<double>::iterator it_l, it_r;
	std::vector<double> r = func->getHyperparameters();
	if (cachedHyperparams.size() != r.size()) return false;
	
	for(it_l = cachedHyperparams.begin(), it_r = r.begin(); it_l != cachedHyperparams.end(); it_l++, it_r++)
	{
		if ((*it_l) != (*it_r)) {
			equal = false;
			break;
		}
	}
	return equal;
}


std::shared_ptr<std::vector<std::vector<double> > > GpDataset::allocateGramMatrix(int n)
{
	if (cachedGramMatrix != nullptr && cachedGramMatrix->size() == (size_t)n
			&& (*cachedGramMatrix)[0].size() == (size_t)n)
		return cachedGramMatrix;
	else
	{
		std::shared_ptr<std::vector<std::vector<double> > > pt = std::make_shared<std::vector<std::vector<double> > >(n);
		for(size_t i = 0; i < pt->size(); ++i) (*pt)[i].resize(n);
		return pt;	
	}
}


std::shared_ptr<std::vector<double> > GpDataset::calculateVariances(std::shared_ptr<KernelFunction> func)
{
	int n = this->getSize();
	std::shared_ptr<std::vector<std::vector<double> > >  x = this->dataX;
	sp_variances = std::make_shared<std::vector<double> >(n);
	for (int i = 0; i < n; i++)
		(*sp_variances)[i] = func->calculate((*x)[i], (*x)[i]);
	return sp_variances;
}

std::shared_ptr<std::vector<std::vector<double> > > GpDataset::calculateCovariances(std::shared_ptr<KernelFunction> func, std::shared_ptr<GpDataset> set)
{
	std::shared_ptr<std::vector<std::vector<double> > > x1 = this->dataX;
	std::shared_ptr<std::vector<std::vector<double> > > x2 = set->dataX;
	const int n1 = this->getSize();
	const int n2 = set->getSize();
	std::shared_ptr<std::vector<std::vector<double> > > result = std::make_shared<std::vector<std::vector<double> >>(n1);
	for (size_t i = 0; i < result->size(); i++) (*result)[i].resize(n2);
	for (int i = 0; i < n1; i++)
		for (int j = 0; j < n2; j++)
			(*result)[i][j] = func->calculate((*x1)[i], (*x2)[j]);
	sp_dblMatrix = result;
	return sp_dblMatrix;
}

bool GpDataset::isModified()
{
	return changedSinceGramCalculation;
}
