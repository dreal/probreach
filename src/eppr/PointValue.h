#ifndef POINTVALUE_H
#define POINTVALUE_H

#include <memory>
#include <vector>

class PointValue
{
public:
	PointValue();
	PointValue(const PointValue& src);
	PointValue(std::shared_ptr<std::vector<double> > point, double value);
	PointValue(std::vector<double>& point, double value);
	~PointValue();

private:
	std::shared_ptr<std::vector<double> > point;
	double value;
public:
	std::shared_ptr<std::vector<double> > getPoint();
	double getValue();
};

#endif