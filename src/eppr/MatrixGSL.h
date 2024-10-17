#ifndef MATRIXGSL_H
#define MATRIXGSL_H

#include <vector>
#include <memory>

class DoubleMatrix;

class IMatrix;

class MatrixGSL : public IMatrix
{
public:
  MatrixGSL(void);
  MatrixGSL(std::shared_ptr<DoubleMatrix> matrixObject);
  virtual ~MatrixGSL(void);
  virtual std::vector<double> &getData();
  virtual int getRows();
  virtual int getColumns();
  virtual int getLength();
  virtual double get(int i, int j);
  virtual void put(int i, int j, double v);
  virtual double get(int i);
  virtual void put(int i, double v);
  virtual std::shared_ptr<IMatrix> getColumn(int i);
  virtual void putColumn(int i, std::shared_ptr<IMatrix> column);

  virtual std::shared_ptr<IMatrix> getRow(int i);

  virtual void putRow(int i, std::shared_ptr<IMatrix> row);

  virtual void copy(std::shared_ptr<IMatrix> arg);

  virtual std::shared_ptr<IMatrix> duplicate();

  virtual std::shared_ptr<IMatrix> transpose();

  virtual int rank();

  virtual std::shared_ptr<IMatrix> add(std::shared_ptr<IMatrix> arg);

  virtual std::shared_ptr<IMatrix> add(double arg);

  virtual std::shared_ptr<IMatrix> sub(std::shared_ptr<IMatrix> arg);

  virtual std::shared_ptr<IMatrix> sub(double arg);

  virtual std::shared_ptr<IMatrix> rsub(std::shared_ptr<IMatrix> arg);

  virtual std::shared_ptr<IMatrix> rsub(double arg);

  virtual std::shared_ptr<IMatrix> mul(std::shared_ptr<IMatrix> arg);

  virtual std::shared_ptr<IMatrix> mul(double arg);

  virtual std::shared_ptr<IMatrix> mmul(std::shared_ptr<IMatrix> arg);

  virtual double dot(std::shared_ptr<IMatrix> arg);

  virtual std::shared_ptr<IMatrix> div(std::shared_ptr<IMatrix> arg);

  virtual std::shared_ptr<IMatrix> div(double arg);

  virtual std::shared_ptr<IMatrix> rdiv(std::shared_ptr<IMatrix> arg);

  virtual std::shared_ptr<IMatrix> rdiv(double arg);

  virtual std::shared_ptr<IMatrix> neg();

  virtual double sum();

  virtual std::shared_ptr<IMatrix> diag();

  virtual std::shared_ptr<IMatrix> repmat(int rows, int columns);

  virtual double max();

  virtual double min();

  virtual std::shared_ptr<IMatrix> sort();

public:
  std::shared_ptr<DoubleMatrix> matrixObject;
  std::shared_ptr<MatrixGSL> resultMatrixObject;

public:
  MatrixGSL(std::vector<double> &data);
  MatrixGSL(std::vector<std::vector<double>> &data);
  MatrixGSL(int n, int m);
  MatrixGSL(int n, int m, double val);
  DoubleMatrix *getMatrixPtr(void);
};

#endif