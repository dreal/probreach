#ifndef REGULARSAMPLER_H
#define REGULARSAMPLER_H

#include "GridSampler.h"

class RegularSampler :
	public GridSampler
{
public:
	RegularSampler(void);
	virtual ~RegularSampler(void);
	virtual std::vector<std::vector<double>>& sample(int n, std::vector<std::shared_ptr<Parameter>>& params); 
	static std::vector<double>& linspace(int n, double a, double b);
};

#endif