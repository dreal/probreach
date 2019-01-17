#include <memory.h>
#include "DoubleMatrix.h"
#include <gsl/gsl_sort.h>
#include <gsl/gsl_sort_vector.h>

DoubleMatrix::DoubleMatrix()
{
	matrix = gsl_matrix_calloc(1, 1);
}

DoubleMatrix::DoubleMatrix(size_t rows, size_t cols)
{
	matrix = gsl_matrix_calloc(rows, cols);
}


DoubleMatrix::DoubleMatrix(std::vector<std::vector<double> >& vect_mat)
{
	size_t rows = vect_mat.size();
	size_t cols = vect_mat[0].size();
	matrix = gsl_matrix_alloc(rows, cols);
	double* data_row = matrix->data;
	for(size_t i = 0; i < rows; ++i) {
		double *data = data_row;
		memcpy(data, &vect_mat[i][0], cols * sizeof(double));
		data_row += matrix->tda;
	}
}

DoubleMatrix::~DoubleMatrix(void)
{
	clear();	
}


void DoubleMatrix::clear(void)
{
	gsl_matrix_free(matrix);
	matrix = NULL;
}



std::shared_ptr<std::vector<std::vector<double> > >& DoubleMatrix::getPtrMatrix(void)
{
	ptr_vector_matrix = std::make_shared<std::vector<std::vector<double> > >(matrix->size1);
	for(size_t i = 0; i < matrix->size1; ++i) {
		(*ptr_vector_matrix)[i].resize(matrix->size2);
		const double* begin_ptr = gsl_matrix_const_ptr(matrix, i, 0);
		const double* end_ptr = gsl_matrix_const_ptr(matrix, i, matrix->size2 - 1) + 1;
		if (begin_ptr != NULL) {
			std::copy(begin_ptr, end_ptr, (*ptr_vector_matrix)[i].begin());
		}
	}
	return ptr_vector_matrix;
}


DoubleMatrix* DoubleMatrix::getColumn(DoubleMatrix& matrix, int col)
{
	DoubleMatrix* m = new DoubleMatrix(matrix.getRows(), 1);
	int rows = matrix.getRows();
	for(int i = 0; i < rows; ++i) {
		double val = matrix.get(i, col);
		m->set(i, 0, val);
	}
	return m;
}


DoubleMatrix* DoubleMatrix::getRow(DoubleMatrix& matrix, int row)
{
	DoubleMatrix* m = new DoubleMatrix(1, matrix.getCols());
	int cols = matrix.getCols();
	const double* data = gsl_matrix_const_ptr(matrix.matrix, row, 0);
	if (NULL == data) return m;
	memcpy(m->matrix->data, data, cols * sizeof(double));
	return m;
}


std::vector<double>& DoubleMatrix::getData(void)
{
	data.resize(matrix->size1 * matrix->size2);
	size_t row_start = 0;
	size_t dest_pos = 0;
	for(size_t r = 0; r < matrix->size1; ++r) {
		std::copy(matrix->data + row_start, matrix->data + row_start + matrix->size2, data.begin() + dest_pos);
		row_start += matrix->tda;
		dest_pos += matrix->size2;
	}
	return data;
}


void DoubleMatrix::putColumn(int c, DoubleMatrix* v)
{
	int rows = getRows();
	for(int i = 0; i < rows; ++i) {
		double val = v->get(i, 0);
		set(i,c,val);
	}
}


void DoubleMatrix::putRow(int r, DoubleMatrix* v)
{
	int cols = getCols();
	double* values = gsl_matrix_ptr(matrix, r, 0);
	memcpy(values, v->matrix->data, cols * sizeof(double)); 
}


void DoubleMatrix::copy(DoubleMatrix* arg)
{
	if (matrix->size1 != arg->matrix->size1 || matrix->size2 != arg->matrix->size2) {
		clear();
		matrix = gsl_matrix_alloc(arg->matrix->size1, arg->matrix->size2);
	}
	//size_t len = arg->matrix->size1 * arg->matrix->tda;
	gsl_matrix_memcpy(matrix, arg->matrix);
	//memcpy(matrix->data, arg->matrix->data, len);
}


DoubleMatrix* DoubleMatrix::dup(void)
{
	DoubleMatrix* m = new DoubleMatrix(getRows(), getCols());
	m->copy(this);
	return m;
}


DoubleMatrix* DoubleMatrix::transpose(void)
{
	DoubleMatrix* m = new DoubleMatrix(getCols(), getRows());
	gsl_matrix_transpose_memcpy(m->matrix, matrix);
	return m;
}


DoubleMatrix* DoubleMatrix::SVDValues(void)
{
	int s = 0;
	int m = (int)matrix->size1;
	int n = (int)matrix->size2;
	//int dim = (m < n) ? m : n;
	gsl_matrix * u = gsl_matrix_alloc(m, n);
	gsl_matrix* q = gsl_matrix_alloc(n, n);
	gsl_vector * d = gsl_vector_alloc(n);
	gsl_vector * x = gsl_vector_calloc(n);
	gsl_matrix_memcpy(u, matrix);
	s += gsl_linalg_SV_decomp(matrix, q, d, x);
	DoubleMatrix* result = new DoubleMatrix(1, n);
	memcpy(result->matrix->data, d->data, n * sizeof(double));
	gsl_vector_free(x);
	gsl_vector_free(d);
	gsl_matrix_free(u);
	gsl_matrix_free(q);
	return result;
}


const double* DoubleMatrix::getConstPtr(int i, int j)
{
	return gsl_matrix_const_ptr(matrix, i, j);
}


DoubleMatrix* DoubleMatrix::add(DoubleMatrix* other)
{
	DoubleMatrix* result = dup();
	gsl_matrix_add(result->matrix, other->matrix);
	return result;
}


DoubleMatrix* DoubleMatrix::add(double arg)
{
	DoubleMatrix* result = dup();
	gsl_matrix_add_constant(result->matrix, arg);
	return result;
}


DoubleMatrix* DoubleMatrix::sub(DoubleMatrix* other)
{
	DoubleMatrix* result = dup();
	gsl_matrix_sub(result->matrix, other->matrix);
	return result;
}


DoubleMatrix* DoubleMatrix::sub(double arg)
{
	DoubleMatrix* result = dup();
	gsl_matrix_add_constant(result->matrix, -arg);
	return result;
}



DoubleMatrix* DoubleMatrix::mul(DoubleMatrix* other)
{
	DoubleMatrix* result = dup();
	gsl_matrix_mul_elements(result->matrix, other->matrix);
	return result;
}


DoubleMatrix* DoubleMatrix::mul(double arg)
{
	DoubleMatrix* result = new DoubleMatrix(matrix->size1, matrix->size2);
	size_t rows = matrix->size1;
	size_t cols = matrix->size2;
	for (size_t r = 0; r < rows; ++r)
	{
		double * val_ptr = gsl_matrix_ptr(result->matrix, r, 0);
		const double * src_ptr = gsl_matrix_const_ptr(matrix, r, 0);
		for (size_t c = 0; c < cols; ++c) {
			*val_ptr = *src_ptr * arg;
			++val_ptr;
			++src_ptr;
		}
	}
	return result;
}


DoubleMatrix* DoubleMatrix::mmul(DoubleMatrix* other)
{
	DoubleMatrix* C = new DoubleMatrix(getRows(), other->getCols());
	gsl_blas_dgemm(CblasNoTrans, CblasNoTrans,
		1.0, matrix, other->matrix, 0.0, C->matrix);
	return C;
}


DoubleMatrix::DoubleMatrix(std::vector<double>& data)
{
	size_t rows = data.size();
	matrix = gsl_matrix_alloc(rows, 1);
	double* data_row = matrix->data;
	for(size_t i = 0; i < rows; ++i) {
		double *tdata = data_row;
		*tdata = data[i];
		data_row += matrix->tda;
	}

}


DoubleMatrix::DoubleMatrix(size_t rows, size_t cols, double val)
{
	matrix = gsl_matrix_alloc(rows, cols);
	for(size_t row = 0; row < rows; ++row) {
		double *ptr_val = gsl_matrix_ptr(matrix, row, 0);
		for(size_t col = 0; col < cols; ++col) {
			*ptr_val++ = val;
		}
	}
}


DoubleMatrix* DoubleMatrix::eye(int n)
{
	DoubleMatrix* result = new DoubleMatrix((size_t)n, (size_t)n);
	for(int i = 0; i < n; ++i) {
		result->set(i, i, 1.0);
	}
	return result;
}


DoubleMatrix* DoubleMatrix::diag(std::vector<double>& data)
{
	DoubleMatrix* result = new DoubleMatrix(data.size(), data.size());
	std::vector<double>::iterator it= data.begin();
	for(int i = 0; i < (int)data.size(); ++i) {
		result->set(i, i, *it++);
	}
	return result;
}


DoubleMatrix* DoubleMatrix::solve(DoubleMatrix* A, DoubleMatrix* B)
{
	//DoubleMatrix* X = new DoubleMatrix(B->matrix->size1, 1);
	//DoubleMatrix* A_ = A->dup();
	//gsl_vector_view v = gsl_matrix_column(B->matrix, 0);
	//gsl_vector* result = gsl_vector_calloc(A->matrix->size1);
	//gsl_linalg_HH_solve(A_->matrix, &v.vector, result);
	//const double* src_ptr = gsl_vector_ptr(&v.vector, 0);
	//for(size_t i = 0; i < X->matrix->size1; i++)
	//	X->set(i, 0, *src_ptr++);
	//delete A_;
	//gsl_vector_free(result);
	//return X;
	DoubleMatrix* X = new DoubleMatrix(B->matrix->size1, B->matrix->size2);
	int signum = 0;
	unsigned long dim = A->matrix->size1;
	gsl_permutation * perm = gsl_permutation_alloc(dim);
	gsl_matrix * lu  = gsl_matrix_alloc(dim,dim);
	gsl_vector * x = gsl_vector_alloc(dim);
	gsl_vector * residual = gsl_vector_alloc(dim);
	gsl_matrix_memcpy(lu,A->matrix);
	gsl_linalg_LU_decomp(lu, perm, &signum);
	for(size_t i = 0; i < B->matrix->size2; i++) {
		gsl_vector_view b = gsl_matrix_column(B->matrix, i);
		gsl_linalg_LU_solve(lu, perm, &b.vector, x);
		gsl_linalg_LU_refine(A->matrix, lu, perm, &b.vector, x, residual);
		gsl_matrix_set_col(X->matrix, i, x);
	}
	gsl_vector_free(residual);
	gsl_vector_free(x);
	gsl_matrix_free(lu);
	gsl_permutation_free(perm);
	return X;
}


DoubleMatrix* DoubleMatrix::cholesky(void)
{
	DoubleMatrix* result = dup();
	gsl_linalg_cholesky_decomp(result->matrix);
	// Decompose.clearLower из Jblas
	for (size_t i = 0; i < result->matrix->size1; i++)
		for (size_t j = i + 1; j < result->matrix->size2; j++)
			gsl_matrix_set(result->matrix, i, j, 0.0);
	DoubleMatrix* transposed = result->transpose();
	delete result;
	return transposed;
}


double DoubleMatrix::det(void)
{
	gsl_permutation * perm = gsl_permutation_alloc(matrix->size1);
	gsl_matrix *lu = gsl_matrix_alloc(matrix->size1, matrix->size1);
	int signum = 0;
	gsl_matrix_memcpy(lu, matrix);
	gsl_linalg_LU_decomp(lu, perm, &signum);
	double det = gsl_linalg_LU_det(lu, signum);
	gsl_matrix_free(lu);
	gsl_permutation_free(perm);
	return det;
}



double DoubleMatrix::dot(DoubleMatrix* other)
{
	gsl_vector_view v1;
	if (matrix->size1 > 1)
		v1 = gsl_matrix_column(matrix, 0);
	else
		v1 = gsl_matrix_row(matrix, 0);
	gsl_vector_view v2;
	if (other->matrix->size1 > 1)
		v2 = gsl_matrix_column(other->matrix, 0);
	else
		v2 = gsl_matrix_row(other->matrix, 0);
	double result = 0.0;
	gsl_blas_ddot(&v1.vector, &v2.vector, &result);
	return result;
}


DoubleMatrix* DoubleMatrix::div(DoubleMatrix* other)
{
	DoubleMatrix* result = dup();
	gsl_matrix_div_elements(result->matrix, other->matrix);
	return result;

}

DoubleMatrix* DoubleMatrix::div(double arg)
{
	DoubleMatrix* result = new DoubleMatrix(matrix->size1, matrix->size2);
	size_t rows = matrix->size1;
	size_t cols = matrix->size2;
	for (size_t r = 0; r < rows; ++r)
	{
		double * val_ptr = gsl_matrix_ptr(result->matrix, r, 0);
		const double * src_ptr = gsl_matrix_const_ptr(matrix, r, 0);
		for (size_t c = 0; c < cols; ++c) {
			*val_ptr = *src_ptr / arg;
			++val_ptr;
			++src_ptr;
		}
	}
	return result;
}

DoubleMatrix* DoubleMatrix::sort()
{
	DoubleMatrix* result = new DoubleMatrix(matrix->size1, matrix->size2);
	gsl_vector* v = gsl_vector_alloc(getLength());
	int pos = 0;
	for(size_t c = 0; c < matrix->size2; c++)
		for (size_t r = 0; r < matrix->size1; r++) {
			double val = gsl_matrix_get(matrix, r, c);
			gsl_vector_set(v, pos++, val);
		}
	gsl_sort_vector(v);
	pos = 0;
	for (size_t c = 0; c < result->matrix->size2; c++)
		for (size_t r = 0; r < result->matrix->size1; r++) {
			double val = gsl_vector_get(v, pos++);
			gsl_matrix_set(result->matrix, r, c, val);
		}
	return result;
}
