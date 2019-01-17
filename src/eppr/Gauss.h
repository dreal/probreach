#ifndef GAUSS_H
#define GAUSS_H

#include <memory>
class IMatrix;

class Gauss
{
public:
	Gauss(void);
	virtual ~Gauss(void);
	std::shared_ptr<IMatrix> LikPar_p;
	std::shared_ptr<IMatrix> LikPar_q;
	std::shared_ptr<IMatrix> xGauss;
	std::shared_ptr<IMatrix> wGauss;
	std::shared_ptr<IMatrix> logwGauss;

	std::shared_ptr<IMatrix> C;
	std::shared_ptr<IMatrix> LC;
	std::shared_ptr<IMatrix> LC_t;
	std::shared_ptr<IMatrix> L;
	std::shared_ptr<IMatrix> W;
	std::shared_ptr<IMatrix> diagV;
	std::shared_ptr<IMatrix> m;
	double logZloo;
	double logZappx;
	std::shared_ptr<IMatrix> logZterms;
	double logZ;
	std::shared_ptr<IMatrix> Term;
};

#endif