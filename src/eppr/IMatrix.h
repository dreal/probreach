#ifndef IMATRIX_H
#define IMATRIX_H

#include <memory>
#include <vector>

class IMatrix {
 public:
  IMatrix(void);
  virtual ~IMatrix(void);
  virtual std::vector<double>& getData() = 0;
  virtual int getRows() = 0;
  virtual int getColumns() = 0;
  virtual int getLength() = 0;
  virtual double get(int i, int j) = 0;
  virtual void put(int i, int j, double v) = 0;
  virtual double get(int i) = 0;
  virtual void put(int i, double v) = 0;
  virtual std::shared_ptr<IMatrix> getColumn(int i) = 0;
  virtual void putColumn(int i, std::shared_ptr<IMatrix> column) = 0;

  virtual std::shared_ptr<IMatrix> getRow(int i) = 0;

  virtual void putRow(int i, std::shared_ptr<IMatrix> row) = 0;

  virtual void copy(std::shared_ptr<IMatrix> arg) = 0;

  virtual std::shared_ptr<IMatrix> duplicate() = 0;

  virtual std::shared_ptr<IMatrix> transpose() = 0;

  virtual int rank() = 0;

  virtual std::shared_ptr<IMatrix> add(std::shared_ptr<IMatrix> arg) = 0;

  virtual std::shared_ptr<IMatrix> add(double arg) = 0;

  virtual std::shared_ptr<IMatrix> sub(std::shared_ptr<IMatrix> arg) = 0;

  virtual std::shared_ptr<IMatrix> sub(double arg) = 0;

  virtual std::shared_ptr<IMatrix> rsub(std::shared_ptr<IMatrix> arg) = 0;

  virtual std::shared_ptr<IMatrix> rsub(double arg) = 0;

  virtual std::shared_ptr<IMatrix> mul(std::shared_ptr<IMatrix> arg) = 0;

  virtual std::shared_ptr<IMatrix> mul(double arg) = 0;

  virtual std::shared_ptr<IMatrix> mmul(std::shared_ptr<IMatrix> arg) = 0;

  virtual double dot(std::shared_ptr<IMatrix> arg) = 0;

  virtual std::shared_ptr<IMatrix> div(std::shared_ptr<IMatrix> arg) = 0;

  virtual std::shared_ptr<IMatrix> div(double arg) = 0;

  virtual std::shared_ptr<IMatrix> rdiv(std::shared_ptr<IMatrix> arg) = 0;

  virtual std::shared_ptr<IMatrix> rdiv(double arg) = 0;

  virtual std::shared_ptr<IMatrix> neg() = 0;

  virtual double sum() = 0;

  virtual std::shared_ptr<IMatrix> diag() = 0;

  virtual std::shared_ptr<IMatrix> repmat(int rows, int columns) = 0;

  virtual double max() = 0;

  virtual double min() = 0;

  virtual std::shared_ptr<IMatrix> sort() = 0;
};

#endif
