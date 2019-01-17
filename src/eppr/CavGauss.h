#ifndef CAVGAUSS_H
#define CAVGAUSS_H

#include <memory>

class IMatrix;

class CavGauss
{
public:
	CavGauss(void);
	virtual ~CavGauss(void);
	std::shared_ptr<IMatrix> diagV;
	std::shared_ptr<IMatrix> m;
};

#endif

