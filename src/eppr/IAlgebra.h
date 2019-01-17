#pragma once

#include <memory>
#include "IMatrix.h"

class IAlgebra
{
public:
	IAlgebra(void);
	virtual ~IAlgebra(void);

	virtual std::shared_ptr<IMatrix> createMatrix(std::vector<double>& data) = 0;

	virtual std::shared_ptr<IMatrix> createMatrix(std::vector<std::vector<double>>& data) = 0;

	virtual std::shared_ptr<IMatrix> createZeros(int n, int m) = 0;

	virtual std::shared_ptr<IMatrix> createOnes(int n, int m) = 0;

	virtual std::shared_ptr<IMatrix> createEye(int n) = 0;

	virtual std::shared_ptr<IMatrix> createDiag (std::vector<double>& data) = 0;

	virtual std::shared_ptr<IMatrix> invert(std::shared_ptr<IMatrix> arg) = 0;

	virtual std::shared_ptr<IMatrix> invertPositive(std::shared_ptr<IMatrix> arg) = 0;

	virtual std::shared_ptr<IMatrix> solve(std::shared_ptr<IMatrix> A, std::shared_ptr<IMatrix> B) = 0;

	virtual std::shared_ptr<IMatrix> solvePositive(std::shared_ptr<IMatrix> A, std::shared_ptr<IMatrix> B) = 0;

	virtual void solvePositiveInPlace(std::shared_ptr<IMatrix> A, std::shared_ptr<IMatrix> B) = 0;

	virtual std::shared_ptr<IMatrix> cholesky(std::shared_ptr<IMatrix> arg) = 0;

	/**
	 * Compute the singular value decomposition: arg = U*S*V'
	 * 
	 * @return An array that holds the matrices: U, S ad V
	 */
	virtual std::vector<std::shared_ptr<IMatrix>>& svd(std::shared_ptr<IMatrix> arg) = 0;

	virtual double determinant(std::shared_ptr<IMatrix> A) = 0;
protected:
	std::shared_ptr<IMatrix> matrix;
	std::vector<std::shared_ptr<IMatrix>> matrix_array;
};

