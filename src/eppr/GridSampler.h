#ifndef GRIDSAMPLER_H
#define GRIDSAMPLER_H

#include <memory>
#include <vector>
#include "Parameter.h"

class GridSampler
{
public:
	GridSampler(void);
	virtual ~GridSampler(void);
	virtual std::vector<std::vector<double>>& sample(int n, std::vector<std::shared_ptr<Parameter>>& params) = 0;
protected:
	std::vector<std::vector<double>> grid;
};

#endif