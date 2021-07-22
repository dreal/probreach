#include "KernelRbfARD.h"

#include <cmath>
#include <limits>
#include "GpDataset.h"


KernelRbfARD::KernelRbfARD(int dimensions)
{

}

KernelRbfARD::KernelRbfARD(std::shared_ptr<std::vector<double> > hyp) {
	setHyperarameters(*hyp.get());
}

KernelRbfARD::~KernelRbfARD()
{
}

void KernelRbfARD::setHyperarameters(std::vector<double>& hyp) {
	this->hyp = std::make_shared<std::vector<double> >(hyp);
	const double a = (*this->hyp)[0];
	this->amplitude2 = a * a;
	this->invLengthscale2 = std::make_shared<std::vector<double> >(this->hyp->size() - 1);
	for (size_t i = 1; i < this->hyp->size(); i++) {
		const double l = (*this->hyp)[i];
		(*invLengthscale2)[i - 1] = 1.0 / (l * l);
	}
}

double KernelRbfARD::calculate(std::vector<double>& x1, std::vector<double>& x2) {
	const size_t dim = x1.size();
	double sum = 0;
	for (size_t i = 0; i < dim; i++) {
		const double v = x1[i] - x2[i];
		sum += v * v * (*invLengthscale2)[i];
	}
	// exp(-0.5 * sum((x1 - x2).^2));
	return amplitude2 * exp(-0.5 * sum);

}
double KernelRbfARD::calculateDerivative(std::vector<double>& x1, std::vector<double>& x2, int i) {
	return -(*invLengthscale2)[i] * (x1[i] - x2[i]) * calculate(x1, x2);
}
double KernelRbfARD::calculateSecondDerivative(std::vector<double>& x1, std::vector<double>& x2, int i, int j) {
	const double k0 = calculate(x1, x2);
	const double ki = 2 * (*invLengthscale2)[i] * (x1[i] - x2[i]);
	const double kj = 2 * (*invLengthscale2)[j] * (x1[j] - x2[j]);
	double k = k0 * ki * kj;
	if (i == j)
		k = k - 2 * (*invLengthscale2)[i] * k0;

	return k;

}
double KernelRbfARD::calculateHyperparamDerivative(std::vector<double>& x1, std::vector<double>& x2, int hyperparamIndex) {
	if (hyperparamIndex < 0 || hyperparamIndex >= (int)hyp->size())
		throw "IllegalStateException()";

	// df(a)/da = 2 * a * exp(-0.5 * x^2 / l^2);
	if (hyperparamIndex == 0) {
		const size_t n = x1.size();
		double sum = 0.0;
		for (size_t i = 0; i < n; i++) {
			const double v = x1[i] - x2[i];
			sum = sum + v * v * (*invLengthscale2)[i];
		}
		return 2 * (*hyp)[0] * exp(-0.5 * sum);
	}
	// df(l)dli = (xi^2 / li^3) * f(li);
	double r2 = x1[hyperparamIndex] - x2[hyperparamIndex];
	r2 *= r2;
	return calculate(x1, x2) * r2 * (*invLengthscale2)[hyperparamIndex]
		/ (*hyp)[hyperparamIndex];

}
std::vector<double>& KernelRbfARD::getHyperparameters(void) {
	return *hyp.get();
}
std::vector<double>& KernelRbfARD::getDefaultHyperarameters(std::shared_ptr<GpDataset> data) {
	defaultHyp = std::make_shared<std::vector<double> >(hyp->size());
	double max, min;

	max = -std::numeric_limits<double>::infinity();
	min = std::numeric_limits<double>::infinity();
	const std::vector<double>& y = data->getTargets();
	for (size_t i = 0; i < y.size(); i++) {
		if (y[i] > max)
			max = y[i];
		if (y[i] < min)
			min = y[i];
	}
	(*defaultHyp)[0] = (max - min) / 2.0;
	if ((*defaultHyp)[0] == 0)
		(*defaultHyp)[0] = 1;

	const int n = data->getSize();
	const int dim = data->getDimension();
	for (int d = 0; d < dim; d++) {
		max = -std::numeric_limits<double>::infinity(); 
		min = std::numeric_limits<double>::infinity();;
		for (int i = 0; i < n; i++) {
			const double curr = data->getInstance(i)[d];
			if (curr > max)
				max = curr;
			if (curr < min)
				min = curr;
		}
		(*defaultHyp)[d + 1] = (max - min) / 10;
	}

	return *defaultHyp.get();

}
