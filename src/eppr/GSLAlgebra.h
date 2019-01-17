#ifndef GSLALGEBRA_H
#define GSLALGEBRA_H

#include "IAlgebra.h"
#include <vector>
#include <memory>

class IMatrix;

class GSLAlgebra :
	public IAlgebra
{
public:
	GSLAlgebra(void);
	virtual ~GSLAlgebra(void);

	virtual std::shared_ptr<IMatrix> createMatrix(std::vector<double>& data);

	virtual std::shared_ptr<IMatrix> createMatrix(std::vector<std::vector<double>>& data);

	virtual std::shared_ptr<IMatrix> createZeros(int n, int m);

	virtual std::shared_ptr<IMatrix> createOnes(int n, int m);

	virtual std::shared_ptr<IMatrix> createEye(int n);

	virtual std::shared_ptr<IMatrix> createDiag (std::vector<double>& data);

	virtual std::shared_ptr<IMatrix> invert(std::shared_ptr<IMatrix> arg);

	virtual std::shared_ptr<IMatrix> invertPositive(std::shared_ptr<IMatrix> arg);

	virtual std::shared_ptr<IMatrix> solve(std::shared_ptr<IMatrix> A, std::shared_ptr<IMatrix> B);

	virtual std::shared_ptr<IMatrix> solvePositive(std::shared_ptr<IMatrix> A, std::shared_ptr<IMatrix> B);

	virtual void solvePositiveInPlace(std::shared_ptr<IMatrix> A, std::shared_ptr<IMatrix> B);

	virtual std::shared_ptr<IMatrix> cholesky(std::shared_ptr<IMatrix> arg);

	/**
	 * Compute the singular value decomposition: arg = U*S*V'
	 * 
	 * @return An array that holds the matrices: U, S ad V
	 */
	virtual std::vector<std::shared_ptr<IMatrix>>& svd(std::shared_ptr<IMatrix> arg);

	virtual double determinant(std::shared_ptr<IMatrix> A) ;
protected:
	std::shared_ptr<IMatrix> resultMatrix;
	std::vector<std::shared_ptr<IMatrix>> SVDResult;
};

#endif