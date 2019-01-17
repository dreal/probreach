#ifndef POWELLMETHODAPACHE_H
#define POWELLMETHODAPACHE_H

#include <memory>
#include <vector>
#include <gsl/gsl_blas.h>
#include <gsl/gsl_multimin.h>
#include <gsl/gsl_math.h>
#include <gsl/gsl_ieee_utils.h>

#include <gsl/gsl_errno.h>

#include "LocalOptimisation.h"
#include "PointValue.h"
class MultivariateFunction;

struct func_params {
	MultivariateFunction* func;
	int n;
};

class PowellMethodApache : public LocalOptimisation
{
public:
	PowellMethodApache(void);
	virtual ~PowellMethodApache(void);
	//virtual std::shared_ptr<PointValue> optimise(std::shared_ptr<ObjectiveFunction> func,
	//	std::shared_ptr<std::vector<double> > init);
	virtual std::shared_ptr<PointValue> optimise(std::shared_ptr<ObjectiveFunction> func,
		std::shared_ptr<std::vector<double> > init);
	func_params fnc_param;
	gsl_multimin_function f;
	std::shared_ptr<PointValue> result;
	std::shared_ptr<std::vector<double> > point;
	static gsl_error_handler_t * old_handler;

	std::vector<std::vector<double> > pointAndDirection;
	std::vector<std::vector<double> >& newPointAndDirection(std::vector<double>& p, std::vector<double>& d, double optimum);
	PointValue srch;
	PointValue& search(std::vector<double>& startPoint, std::vector<double>& direction);
	bool converged(int iteration, PointValue& previous, PointValue& current);
};

#endif
