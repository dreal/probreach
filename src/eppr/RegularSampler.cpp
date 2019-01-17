#include "RegularSampler.h"
#include <cmath>
#include <vector>

RegularSampler::RegularSampler(void)
{
}


RegularSampler::~RegularSampler(void)
{
}

std::vector<std::vector<double>>& RegularSampler::sample(int n, std::vector<std::shared_ptr<Parameter>>& params) {
		const int dim = params.size();
		const int pointsPerDim = (int) ceil(pow(n, 1.0 / dim));
		const int nPrime = (int) pow((double)pointsPerDim, dim);

		grid.clear();
		grid.resize(nPrime);
		for(int i = 0; i < dim; ++i) grid[i].resize(dim);
		for (int d = dim - 1; d >= 0; d--) {
			const std::vector<double>& lin = linspace(pointsPerDim,
					params[d]->getLowerBound(), params[d]->getUpperBound());

			const int repsRequired = (int) pow((double)pointsPerDim, dim - d - 1);
			int j = 0;
			int reps = 0;
			for (int i = 0; i < nPrime; i++) {
				grid[i][d] = lin[j];
				if (++reps >= repsRequired) {
					reps = 0;
					if (++j >= pointsPerDim)
						j = 0;
				}
			}
		}
		return grid;
}

std::vector<double> x;

std::vector<double>& RegularSampler::linspace(int n, double a, double b)
{
		const double step = (b - a) / (n - 1);
		double current = a;
		x.clear();
		for (int i = 0; i < n; i++) {
			x.push_back(current);
			current += step;
		}
		return x;
}
