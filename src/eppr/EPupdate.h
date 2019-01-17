#ifndef EPUPDATE_H
#define EPUPDATE_H

#include<memory>

class IMatrix;

class EPupdate
{
public:
	EPupdate(void);
	virtual ~EPupdate(void);
	std::shared_ptr<IMatrix> TermNew;
	std::shared_ptr<IMatrix> logZterms;
	std::shared_ptr<IMatrix> logZ;
};

#endif