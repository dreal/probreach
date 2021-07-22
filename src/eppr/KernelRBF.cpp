#include "KernelRBF.h"
#include <limits>
#include <cmath>

KernelRBF::KernelRBF(void)
{
	std::vector<double> v;
	v.push_back(1);
	v.push_back(1);
	setHyperarameters(v);
}


KernelRBF::~KernelRBF(void)
{
}

double KernelRBF::calculate(std::vector<double>& x1, std::vector<double>& x2) {
		const int n = x1.size();
		double sum = 0;
		for (int i = 0; i < n; i++) {
			const double v = x1[i] - x2[i];
			sum += v * v;
		}
		// exp(-0.5 * sum((x1 - x2).^2));
		return amplitude2 * std::exp(-0.5 * sum * invLengthscale2);
}

double KernelRBF::calculateDerivative(std::vector<double>& x1, std::vector<double>& x2, int i) {
	return -invLengthscale2 * (x1[i] - x2[i]) * calculate(x1, x2);
}

double KernelRBF::calculateSecondDerivative(std::vector<double>& x1, std::vector<double>& x2, int i, int j) {
		const double k0 = calculate(x1, x2);
		const double ki = 2 * invLengthscale2 * (x1[i] - x2[i]);
		const double kj = 2 * invLengthscale2 * (x1[j] - x2[j]);
		double k = k0 * ki * kj;
		if (i == j)
			k = k - 2 * invLengthscale2 * k0;
		return k;

}

double KernelRBF::calculateHyperparamDerivative(std::vector<double>& x1, std::vector<double>& x2, int hyperparamIndex) {
		const int n = x1.size();
		double sum = 0;
		for (int i = 0; i < n; i++) {
			const double v = x1[i] - x2[i];
			sum += v * v;
		}

		// df(a)/da = 2 * a * exp(-0.5 * x^2 / l^2);
		if (hyperparamIndex == 0)
			return 2 * hyp[0] * std::exp(-0.5 * sum * invLengthscale2);

		// df(l)/dl = (x^2 / l^3) * f(l);
		if (hyperparamIndex == 1)
			return calculate(x1, x2) * sum * invLengthscale2 / hyp[1];

		throw "IllegalStateException()";

}

std::vector<double>& KernelRBF::getHyperparameters(void) {
	return hyp;
}

std::vector<double>& KernelRBF::getDefaultHyperarameters(std::shared_ptr<GpDataset> data) {
	defaultHyp.resize(hyp.size());
		double max, min;

		max = std::numeric_limits<double>::infinity();
		min = -std::numeric_limits<double>::infinity();
		const std::vector<double>& y = data->getTargets();
		for (size_t i = 0; i < y.size(); i++) {
			if (y[i] > max)
				max = y[i];
			if (y[i] < min)
				min = y[i];
		}
		defaultHyp[0] = (max - min) / 2.0;
		if (defaultHyp[0] == 0)
			defaultHyp[0] = 1;

		double sum = 0;
		const int n = data->getSize();
		const int dim = data->getDimension();
		for (int d = 0; d < dim; d++) {
			max = -std::numeric_limits<double>::infinity();
			min = -std::numeric_limits<double>::infinity();
			for (int i = 0; i < n; i++) {
				const std::shared_ptr<std::vector<std::vector<double> > >& xcur = data->getInstance();
				double curr = (*xcur)[i][d];
				if (curr > max)
					max = curr;
				if (curr < min)
					min = curr;
			}
			sum += (max - min) / 10.0;
		}
		defaultHyp[1] = sum / dim;

		return defaultHyp;
}

void KernelRBF::setHyperarameters(std::vector<double>& hyp) {
		this->hyp = hyp;
		const double a = hyp[0];
		const double l = hyp[1];
		this->amplitude2 = a * a;
		this->invLengthscale2 = 1.0 / (l * l);
}

KernelRBF::KernelRBF(double a, double l)
{
	std::vector<double> v;
	v.push_back(a);
	v.push_back(l);
	setHyperarameters(v);
}
