#ifndef DOUBLEMATRIX_H
#define DOUBLEMATRIX_H

#include <gsl/gsl_matrix.h>
#include <gsl/gsl_linalg.h>
#include <gsl/gsl_blas.h>
#include <memory>
#include <vector>

class DoubleMatrix
{
public:
  DoubleMatrix();
  DoubleMatrix(size_t rows, size_t cols);
  DoubleMatrix(std::vector<std::vector<double>> &vect_mat);
  ~DoubleMatrix(void);

public:
  gsl_matrix *matrix;
  std::shared_ptr<std::vector<std::vector<double>>> ptr_vector_matrix;
  std::vector<double> data;
  void clear(void);

public:
  double get(int r, int c)
  {
    return gsl_matrix_get(matrix, (size_t)r, (size_t)c);
  }

  void set(int r, int c, double v)
  {
    gsl_matrix_set(matrix, (size_t)r, (size_t)c, v);
  }
  std::shared_ptr<std::vector<std::vector<double>>> &getPtrMatrix(void);

  int getRows(void)
  {
    return (int)matrix->size1;
  }

  int getCols(void)
  {
    return (int)matrix->size2;
  }

  int getLength(void)
  {
    return (int)matrix->size1 * (int)matrix->size2;
  }
  static DoubleMatrix *getColumn(DoubleMatrix &matrix, int col);
  static DoubleMatrix *getRow(DoubleMatrix &matrix, int row);
  std::vector<double> &getData(void);
  void putColumn(int c, DoubleMatrix *v);
  void putRow(int r, DoubleMatrix *v);
  void copy(DoubleMatrix *arg);
  DoubleMatrix *dup(void);
  DoubleMatrix *transpose(void);
  DoubleMatrix *SVDValues(void);
  const double *getConstPtr(int i, int j);
  DoubleMatrix *add(DoubleMatrix *other);
  DoubleMatrix *add(double arg);
  DoubleMatrix *sub(DoubleMatrix *other);
  DoubleMatrix *sub(double arg);
  DoubleMatrix *mul(DoubleMatrix *other);
  DoubleMatrix *mul(double arg);
  DoubleMatrix *mmul(DoubleMatrix *other);
  DoubleMatrix(std::vector<double> &data);
  DoubleMatrix(size_t rows, size_t cols, double val);
  static DoubleMatrix *eye(int n);
  static DoubleMatrix *diag(std::vector<double> &data);
  static DoubleMatrix *solve(DoubleMatrix *A, DoubleMatrix *B);
  DoubleMatrix *cholesky(void);
  double det(void);
  double dot(DoubleMatrix *other);
  DoubleMatrix *div(DoubleMatrix *other);
  DoubleMatrix *div(double arg);
  DoubleMatrix *sort();
};

#endif
