#ifndef DEBUGLOGMATRIX_H
#define DEBUGLOGMATRIX_H

#include <memory>
#include <vector>
#include <gsl/gsl_matrix.h>


//#include "MatrixGSL.h"
//#include "DoubleMatrix.h"
//
//#define S1(x) #x
//#define EXTRACT_MATRIX(arg) (((MatrixGSL*)S1(arg).get())->matrixObject->matrix)

class DebugLogMatrix
{
public:
	DebugLogMatrix();
	~DebugLogMatrix();
	static void printMatrix(char* desc, int id, std::shared_ptr<std::vector<double> > arg);
	static void printMatrix(char* desc, int id, std::vector<double>& arg);
	static void printMatrix(char* desc, int id, gsl_vector* arg);
	static void printMatrix(char* desc, int id, std::shared_ptr<std::vector<std::vector<double> > > arg);
	static void printMatrix(char* desc, int id, std::vector<std::vector<double> >&  arg);
	static void printMatrix(char* desc, int id, gsl_matrix* arg);
	static void printMatrix(char* desc, int id, double arg);
};
#endif
