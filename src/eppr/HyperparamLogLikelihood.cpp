#include "HyperparamLogLikelihood.h"
#include <cmath>
#include <limits>
#include <memory.h>
#include "AbstractGP.h"
#include "KernelFunction.h"
#include <gsl/gsl_math.h>

#include <stdio.h>

HyperparamLogLikelihood::HyperparamLogLikelihood(std::shared_ptr<AbstractGP> gp, bool logspace)
{
	this->gp = gp;
	this->logspace = logspace;
}


HyperparamLogLikelihood::~HyperparamLogLikelihood()
{
}


double HyperparamLogLikelihood::getValueAt(std::shared_ptr<std::vector<double> > point)
{
	std::shared_ptr<std::vector<double> > vec = std::make_shared<std::vector<double> >(point->size());
	std::copy(point->begin(), point->end(), vec->begin());

	if (logspace)
		for (size_t i = 0; i < vec->size(); i++)
			(*vec)[i] = exp((*vec)[i]);
	gp->getKernel()->setHyperarameters(*vec.get());
	double lik = GSL_NAN;//-std::numeric_limits<double>::infinity();
	try {
		lik = gp->getMarginalLikelihood();
	}
	catch (const char* e) {
		int err = strcmp(e, "cholesky");
		if (err != 0)
			throw e;
	  //	  printf("Exception\n");
	}
	return lik;
}


std::shared_ptr<std::vector<double> > HyperparamLogLikelihood::getGradientAt(std::shared_ptr<std::vector<double> > point)
{
	std::shared_ptr<std::vector<double> > vec = std::make_shared<std::vector<double> >(point->size());
	std::copy(point->begin(), point->end(), vec->begin());
	if (logspace)
		for (size_t i = 0; i < vec->size(); i++)
			(*vec)[i]= exp((*vec)[i]);
	gp->getKernel()->setHyperarameters(*vec.get());
	try {
		std::shared_ptr<std::vector<double> > grad = gp->getMarginalLikelihoodGradient();
		return grad;
	}
	catch (const char e) {
		throw (e);
	}

}

