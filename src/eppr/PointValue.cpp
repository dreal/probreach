#include "PointValue.h"

PointValue::PointValue() {
	this->point = nullptr;
	this->value = 0.0;
}

PointValue::PointValue(const PointValue& src)
{
	std::vector<double> *pt = src.point.get();
	this->point = std::make_shared<std::vector<double> >(*pt);
	this->value = src.value;
}

PointValue::PointValue(std::shared_ptr<std::vector<double> > point, double value)
{
	this->point = point;
	this->value = value;
}

PointValue::PointValue(std::vector<double>& point, double value) {
	this->point = std::make_shared<std::vector<double> >(point);
	this->value = value;
}
PointValue::~PointValue()
{
}


std::shared_ptr<std::vector<double> > PointValue::getPoint()
{
	return point;
}


double PointValue::getValue()
{
	return value;
}
