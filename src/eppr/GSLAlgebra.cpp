#include "GSLAlgebra.h"
#include "IMatrix.h"
#include "MatrixGSL.h"
#include "DoubleMatrix.h"

GSLAlgebra::GSLAlgebra(void)
{
}


GSLAlgebra::~GSLAlgebra(void)
{
}

	std::shared_ptr<IMatrix> GSLAlgebra::createMatrix(std::vector<double>& data){
		resultMatrix = std::make_shared<MatrixGSL>(data);
		return resultMatrix;
	}

	std::shared_ptr<IMatrix> GSLAlgebra::createMatrix(std::vector<std::vector<double>>& data){
		resultMatrix = std::make_shared<MatrixGSL>(data);
		return resultMatrix;
	}

	std::shared_ptr<IMatrix> GSLAlgebra::createZeros(int n, int m){
		resultMatrix = std::make_shared<MatrixGSL>(n, m);
		return resultMatrix;
	}

	std::shared_ptr<IMatrix> GSLAlgebra::createOnes(int n, int m){
		resultMatrix = std::make_shared<MatrixGSL>(n, m, 1.0);
		return resultMatrix;
	}

	std::shared_ptr<IMatrix> GSLAlgebra::createEye(int n){
		DoubleMatrix* eye = DoubleMatrix::eye(n);
		std::shared_ptr<DoubleMatrix> m(eye);
		resultMatrix = std::make_shared<MatrixGSL>(m);
		return resultMatrix;
	}

	std::shared_ptr<IMatrix> GSLAlgebra::createDiag (std::vector<double>& data){
		DoubleMatrix* eye = DoubleMatrix::diag(data);
		std::shared_ptr<DoubleMatrix> m(eye);
		resultMatrix = std::make_shared<MatrixGSL>(m);
		return resultMatrix;
	}

	std::shared_ptr<IMatrix> GSLAlgebra::invert(std::shared_ptr<IMatrix> arg){
		return solve(arg, createEye(arg->getRows()));;
	}

	std::shared_ptr<IMatrix> GSLAlgebra::invertPositive(std::shared_ptr<IMatrix> arg){
		return solvePositive(arg, createEye(arg->getRows()));;
	}

	std::shared_ptr<IMatrix> GSLAlgebra::solve(std::shared_ptr<IMatrix> A, std::shared_ptr<IMatrix> B){
		MatrixGSL* A_ = dynamic_cast<MatrixGSL*>(A.get());
		MatrixGSL* B_ = dynamic_cast<MatrixGSL*>(B.get());
		DoubleMatrix* X = DoubleMatrix::solve(A_->getMatrixPtr(), B_->getMatrixPtr());
		std::shared_ptr<DoubleMatrix> m(X);
		resultMatrix = std::make_shared<MatrixGSL>(m);
		return resultMatrix;
	}

	std::shared_ptr<IMatrix> GSLAlgebra::solvePositive(std::shared_ptr<IMatrix> A, std::shared_ptr<IMatrix> B){
		MatrixGSL* A_ = dynamic_cast<MatrixGSL*>(A.get());
		MatrixGSL* B_ = dynamic_cast<MatrixGSL*>(B.get());
		DoubleMatrix* X = DoubleMatrix::solve(A_->getMatrixPtr(), B_->getMatrixPtr());
		std::shared_ptr<DoubleMatrix> m(X);
		resultMatrix = std::make_shared<MatrixGSL>(m);
		return resultMatrix;
	}

	void GSLAlgebra::solvePositiveInPlace(std::shared_ptr<IMatrix> A, std::shared_ptr<IMatrix> B){
		MatrixGSL* A_ = dynamic_cast<MatrixGSL*>(A.get());
		MatrixGSL* B_ = dynamic_cast<MatrixGSL*>(B.get());
		DoubleMatrix* X = DoubleMatrix::solve(A_->getMatrixPtr(), B_->getMatrixPtr());
		std::shared_ptr<DoubleMatrix> m(X);
		B->copy(std::make_shared<MatrixGSL>(m));
	}

	std::shared_ptr<IMatrix> GSLAlgebra::cholesky(std::shared_ptr<IMatrix> arg){
		MatrixGSL* arg_ = dynamic_cast<MatrixGSL*>(arg.get());
		DoubleMatrix* X = arg_->getMatrixPtr()->cholesky();
		std::shared_ptr<DoubleMatrix> m(X);
		resultMatrix = std::make_shared<MatrixGSL>(m);
		return resultMatrix;
	}

/**
	* Compute the singular value decomposition: arg = U*S*V'
	* 
	* @return An array that holds the matrices: U, S ad V
	*/
	std::vector<std::shared_ptr<IMatrix>>& GSLAlgebra::svd(std::shared_ptr<IMatrix> arg){
		throw "Not implemented";
		return SVDResult;
	}

	double GSLAlgebra::determinant(std::shared_ptr<IMatrix> A) {
		MatrixGSL* arg_ = dynamic_cast<MatrixGSL*>(A.get());
		return arg_->getMatrixPtr()->det();
	}