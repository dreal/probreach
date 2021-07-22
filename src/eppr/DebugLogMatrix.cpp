#include "DebugLogMatrix.h"
#include <fstream>
#include <string>
using namespace std;

DebugLogMatrix::DebugLogMatrix()
{
}


DebugLogMatrix::~DebugLogMatrix()
{
}


void DebugLogMatrix::printMatrix(char* desc, int id, std::shared_ptr<std::vector<double> > arg)
{
  //#ifdef _DEBUG
	ofstream out;
	out.open("log.txt", ios_base::app);
	out << string(desc) << " " << id << endl << "------" << endl;
	if (nullptr == arg) {
		out << "nullptr" << endl << endl;
		return;
	}
	out << "length=" << arg->size() << endl;
	for (size_t i = 0; i < arg->size(); i++) {
		//out << "arg[" << i << "]=" << (*arg)[i] << endl;
		out << (*arg)[i] << endl;
	}
	out << endl;
	//#endif
}
void DebugLogMatrix::printMatrix(char* desc, int id, std::vector<double>& arg) {
  //#ifdef _DEBUG
	ofstream out;
	out.open("log.txt", ios_base::app);
	out << string(desc) << " " << id << endl << "------" << endl;
	out << "length=" << arg.size() << endl;
	for (size_t i = 0; i < arg.size(); i++) {
		//out << "arg[" << i << "]=" << arg[i] << endl;
		out << arg[i] << endl;
	}
	out << endl;
	//#endif
}

void DebugLogMatrix::printMatrix(char* desc, int id, gsl_vector* arg) {
  //#ifdef _DEBUG
	ofstream out;
	out.open("log.txt", ios_base::app);
	out << string(desc) << " " << id << endl << "------" << endl;
	out << "length=" << arg->size << endl;
	for (size_t i = 0; i < arg->size; i++) {
		//out << "arg[" << i << "]=" << gsl_vector_get(arg,i) << endl;
		out << gsl_vector_get(arg,i) << endl;
	}
	out << endl;
	//#endif
}

void DebugLogMatrix::printMatrix(char* desc, int id, std::shared_ptr<std::vector<std::vector<double> > > arg)
{
  //#ifdef _DEBUG
	ofstream out;
	out.open("log.txt", ios_base::app);
	out << string(desc) << " " << id << endl << "------" << endl;
	if (nullptr == arg) {
		out << "nullptr" << endl << endl;
		return;
	}
	size_t rows = arg->size();
	size_t cols = (*arg)[0].size();
	out << "rows=" << rows << " cols=" << cols << " length=" << rows * cols << endl;
	for (size_t i = 0; i < rows; i++) {
		for (size_t j = 0; j < cols; j++) {
			out << "arg[" << i * cols + j << "] = arg[" << i << "][" << j << "]=" << (*arg)[i][j] << endl;
		}
	}
	out << endl;
	//#endif
}

void DebugLogMatrix::printMatrix(char* desc, int id, std::vector<std::vector<double> >&  arg) {
  //#ifdef _DEBUG
	ofstream out;
	out.open("log.txt", ios_base::app);
	out << string(desc) << " " << id << endl << "------" << endl;
	size_t rows = arg.size();
	size_t cols = arg[0].size();
	out << "rows=" << rows << " cols=" << cols << " length=" << rows * cols << endl;
	for (size_t i = 0; i < rows; i++) {
		for (size_t j = 0; j < cols; j++) {
			out << "arg[" << i * cols + j << "] = arg[" << i << "][" << j << "]=" << arg[i][j] << endl;
		}
	}
	out << endl;
	//#endif

}
void DebugLogMatrix::printMatrix(char* desc, int id, gsl_matrix* arg) {
  //#ifdef _DEBUG
	ofstream out;
	out.open("log.txt", ios_base::app);
	out << string(desc) << " " << id << endl << "------" << endl;
	size_t rows = arg->size1;
	size_t cols = arg->size2;
	out << "rows=" << rows << " cols=" << cols << " length=" << rows * cols << endl;
	for (size_t j = 0; j < cols; j++) {
		for (size_t i = 0; i < rows; i++) {
			out << "arg[" << j * rows + i << "] = arg[" << i << "][" << j << "]=" << gsl_matrix_get(arg, i, j) << endl;
		}
	}
	out << endl;
	//#endif
}

void DebugLogMatrix::printMatrix(char* desc, int id, double arg) {
  //#ifdef _DEBUG
	ofstream out;
	out.open("log.txt", ios_base::app);
	out << string(desc) << " " << id << endl << "------" << endl;
	out << "arg=" << arg << endl << endl;
	//#endif
}
