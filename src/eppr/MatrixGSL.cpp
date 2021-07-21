#include "MatrixGSL.h"

#include <limits>

#include "DoubleMatrix.h"
#include "IMatrix.h"

MatrixGSL::MatrixGSL(void) { matrixObject = nullptr; }

MatrixGSL::MatrixGSL(std::shared_ptr<DoubleMatrix> matrixObject) {
  this->matrixObject = matrixObject;
}

MatrixGSL::~MatrixGSL(void) {}

std::vector<double>& MatrixGSL::getData() { return matrixObject->getData(); }
int MatrixGSL::getRows() { return matrixObject->getRows(); }
int MatrixGSL::getColumns() { return matrixObject->getCols(); }
int MatrixGSL::getLength() { return matrixObject->getLength(); }
double MatrixGSL::get(int i, int j) { return matrixObject->get(i, j); }
void MatrixGSL::put(int i, int j, double v) { matrixObject->set(i, j, v); }
double MatrixGSL::get(int i) {
  // int r = i / matrixObject->getRows();
  // int c = i % matrixObject->getCols();
  int c = i / matrixObject->getRows();
  int r = i % matrixObject->getRows();
  return get(r, c);
}
void MatrixGSL::put(int i, double v) {
  // int r = i / matrixObject->getRows();
  // int c = i % matrixObject->getCols();
  int c = i / matrixObject->getRows();
  int r = i % matrixObject->getRows();
  put(r, c, v);
}
std::shared_ptr<IMatrix> MatrixGSL::getColumn(int i) {
  std::shared_ptr<DoubleMatrix> sp(DoubleMatrix::getColumn(*matrixObject, i));
  resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  return resultMatrixObject;
}
void MatrixGSL::putColumn(int i, std::shared_ptr<IMatrix> column) {
  MatrixGSL* m = dynamic_cast<MatrixGSL*>(column.get());
  if (NULL != m) {
    matrixObject->putColumn(i, m->matrixObject.get());
  } else
    throw "putColumn failed";
}

std::shared_ptr<IMatrix> MatrixGSL::getRow(int i) {
  std::shared_ptr<DoubleMatrix> sp(DoubleMatrix::getRow(*matrixObject, i));
  resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  return resultMatrixObject;
}

void MatrixGSL::putRow(int i, std::shared_ptr<IMatrix> row) {
  MatrixGSL* m = dynamic_cast<MatrixGSL*>(row.get());
  if (NULL != m) {
    matrixObject->putRow(i, m->matrixObject.get());
  } else
    throw "putRow failed";
}

void MatrixGSL::copy(std::shared_ptr<IMatrix> arg) {
  MatrixGSL* m = dynamic_cast<MatrixGSL*>(arg.get());
  if (NULL != m) {
    matrixObject->copy(m->matrixObject.get());
  } else
    throw "copy failed";
}

std::shared_ptr<IMatrix> MatrixGSL::duplicate() {
  std::shared_ptr<DoubleMatrix> sp(matrixObject->dup());
  resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  return resultMatrixObject;
}

std::shared_ptr<IMatrix> MatrixGSL::transpose() {
  std::shared_ptr<DoubleMatrix> sp(matrixObject->transpose());
  resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  return resultMatrixObject;
}

int MatrixGSL::rank() {
  DoubleMatrix* v = matrixObject->SVDValues();
  double machineEpsilon = std::numeric_limits<double>::epsilon();
  int len = v->getLength();
  int nonzero = 0;
  const double* data = v->getConstPtr(0, 0);
  for (int i = 0; i < len; ++i)
    if (abs(*data++) > machineEpsilon) nonzero++;
  delete v;
  return nonzero;
}

std::shared_ptr<IMatrix> MatrixGSL::add(std::shared_ptr<IMatrix> arg) {
  MatrixGSL* m = dynamic_cast<MatrixGSL*>(arg.get());
  DoubleMatrix* result;
  if (NULL != m) {
    result = matrixObject->add(m->matrixObject.get());
    std::shared_ptr<DoubleMatrix> sp(result);
    resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  }
  return resultMatrixObject;
}

std::shared_ptr<IMatrix> MatrixGSL::add(double arg) {
  DoubleMatrix* result = matrixObject->add(arg);
  std::shared_ptr<DoubleMatrix> sp(result);
  resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  return resultMatrixObject;
}

std::shared_ptr<IMatrix> MatrixGSL::sub(std::shared_ptr<IMatrix> arg) {
  DoubleMatrix* result;
  MatrixGSL* m = dynamic_cast<MatrixGSL*>(arg.get());
  if (NULL != m) {
    result = matrixObject->sub(m->matrixObject.get());
    std::shared_ptr<DoubleMatrix> sp(result);
    resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  }
  return resultMatrixObject;
}

std::shared_ptr<IMatrix> MatrixGSL::sub(double arg) {
  DoubleMatrix* result = matrixObject->sub(arg);
  std::shared_ptr<DoubleMatrix> sp(result);
  resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  return resultMatrixObject;
}

std::shared_ptr<IMatrix> MatrixGSL::rsub(std::shared_ptr<IMatrix> arg) {
  //	MatrixGSL* m = dynamic_cast<MatrixGSL*>(arg.get());
  return (arg->sub(duplicate()));
}

std::shared_ptr<IMatrix> MatrixGSL::rsub(double arg) {
  DoubleMatrix* m = new DoubleMatrix(getRows(), getColumns());
  std::shared_ptr<DoubleMatrix> sp(m);
  resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  int len = resultMatrixObject->getLength();
  for (int i = 0; i < len; ++i)
    resultMatrixObject->put(i, arg - resultMatrixObject->get(i));
  return resultMatrixObject;
}

std::shared_ptr<IMatrix> MatrixGSL::mul(std::shared_ptr<IMatrix> arg) {
  MatrixGSL* m = dynamic_cast<MatrixGSL*>(arg.get());
  if (NULL != m) {
    DoubleMatrix* result = matrixObject->mul(m->matrixObject.get());
    std::shared_ptr<DoubleMatrix> sp(result);
    resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  }
  return resultMatrixObject;
}

std::shared_ptr<IMatrix> MatrixGSL::mul(double arg) {
  DoubleMatrix* result = matrixObject->mul(arg);
  std::shared_ptr<DoubleMatrix> m(result);
  resultMatrixObject = std::make_shared<MatrixGSL>(m);
  return resultMatrixObject;
}

std::shared_ptr<IMatrix> MatrixGSL::mmul(std::shared_ptr<IMatrix> arg) {
  MatrixGSL* m = dynamic_cast<MatrixGSL*>(arg.get());
  if (NULL != m) {
    DoubleMatrix* result = matrixObject->mmul(m->matrixObject.get());
    std::shared_ptr<DoubleMatrix> sp(result);
    resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  }
  return resultMatrixObject;
}

double MatrixGSL::dot(std::shared_ptr<IMatrix> arg) {
  MatrixGSL* m = dynamic_cast<MatrixGSL*>(arg.get());
  if (NULL != m) {
    return matrixObject->dot(m->matrixObject.get());
  }

  return 0.0;
}

std::shared_ptr<IMatrix> MatrixGSL::div(std::shared_ptr<IMatrix> arg) {
  MatrixGSL* m = dynamic_cast<MatrixGSL*>(arg.get());
  if (NULL != m) {
    DoubleMatrix* result = matrixObject->div(m->matrixObject.get());
    std::shared_ptr<DoubleMatrix> sp(result);
    resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  }
  return resultMatrixObject;
}

std::shared_ptr<IMatrix> MatrixGSL::div(double arg) {
  DoubleMatrix* result = matrixObject->div(arg);
  std::shared_ptr<DoubleMatrix> m(result);
  resultMatrixObject = std::make_shared<MatrixGSL>(m);
  return resultMatrixObject;
}

std::shared_ptr<IMatrix> MatrixGSL::rdiv(std::shared_ptr<IMatrix> arg) {
  throw "Not implemented";
  return resultMatrixObject;
}

std::shared_ptr<IMatrix> MatrixGSL::rdiv(double arg) {
  throw "Not implemented";
  return resultMatrixObject;
}

std::shared_ptr<IMatrix> MatrixGSL::neg() {
  DoubleMatrix* result = matrixObject->dup();
  for (int i = 0; i < getRows(); i++)
    for (int j = 0; j < getColumns(); j++) {
      result->set(i, j, -get(i, j));
    }
  std::shared_ptr<DoubleMatrix> sp(result);
  resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  return resultMatrixObject;
}

double MatrixGSL::sum() {
  double s = 0.0;
  for (int i = 0; i < getLength(); i++) s = s + get(i);
  return s;
}

std::shared_ptr<IMatrix> MatrixGSL::diag() {
  DoubleMatrix* result = new DoubleMatrix(getRows(), 1);
  for (int i = 0; i < getRows(); i++) {
    result->set(i, 0, get(i, i));
  }
  std::shared_ptr<DoubleMatrix> sp(result);
  resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  return resultMatrixObject;
}

std::shared_ptr<IMatrix> MatrixGSL::repmat(int rowMult, int columnMult) {
  DoubleMatrix* result =
      new DoubleMatrix(getRows() * rowMult, getColumns() * columnMult);
  for (int c = 0; c < columnMult; c++) {
    for (int r = 0; r < rowMult; r++) {
      for (int i = 0; i < getRows(); i++) {
        for (int j = 0; j < getColumns(); j++) {
          result->set(r * getRows() + i, c * getColumns() + j, get(i, j));
        }
      }
    }
  }
  std::shared_ptr<DoubleMatrix> sp(result);
  resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  return resultMatrixObject;
}

double MatrixGSL::max() {
  if (matrixObject == nullptr) return -std::numeric_limits<double>::infinity();
  if (matrixObject->getLength() == 0)
    return -std::numeric_limits<double>::infinity();
  double v = -std::numeric_limits<double>::infinity();
  for (int i = 0; i < getLength(); ++i) {
    if (((get(i) == get(i)) && (get(i) > v))) {  // !isNaN
      v = get(i);
    }
  }
  return v;
}

double MatrixGSL::min() {
  if (matrixObject == nullptr) return std::numeric_limits<double>::infinity();
  if (matrixObject->getLength() == 0)
    return std::numeric_limits<double>::infinity();
  double v = std::numeric_limits<double>::infinity();
  for (int i = 0; i < getLength(); ++i) {
    if (((get(i) == get(i)) && (get(i) < v))) {  // !isNaN
      v = get(i);
    }
  }
  return v;
}

std::shared_ptr<IMatrix> MatrixGSL::sort() {
  DoubleMatrix* result = matrixObject->sort();
  std::shared_ptr<DoubleMatrix> sp(result);
  resultMatrixObject = std::make_shared<MatrixGSL>(sp);
  return resultMatrixObject;
}

MatrixGSL::MatrixGSL(std::vector<double>& data) {
  this->matrixObject = std::make_shared<DoubleMatrix>(data);
}

MatrixGSL::MatrixGSL(std::vector<std::vector<double> >& data) {
  this->matrixObject = std::make_shared<DoubleMatrix>(data);
}

MatrixGSL::MatrixGSL(int n, int m) {
  this->matrixObject = std::make_shared<DoubleMatrix>((size_t)n, (size_t)m);
}

MatrixGSL::MatrixGSL(int n, int m, double val) {
  this->matrixObject =
      std::make_shared<DoubleMatrix>((size_t)n, (size_t)m, val);
}

DoubleMatrix* MatrixGSL::getMatrixPtr(void) { return matrixObject.get(); }
