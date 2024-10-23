#include <string.h>
#include <stdio.h>
#include "PowellMethodApache.h"

#include <gsl/gsl_test.h>
#include "PointValue.h"
#include "ObjectiveFunction.h"
#include "MultivariateFunction.h"

gsl_error_handler_t *PowellMethodApache::old_handler = NULL;

void handler(const char *reason, const char *file, int line, int gsl_errno)
{
  int error = strcmp("matrix must be positive definite", reason);
  int error1 = strcmp("matrix is not positive definite", reason);
  int error2 = strcmp("contraction failed", reason);
  if (0 == error || 0 == error1)
    throw "cholesky"; //"matrix is not positive definite";
  else if (0 == error2)
  {
    throw "gsl_multimin_fminimizer_iterate";
  }

  {
    if (NULL != PowellMethodApache::old_handler)
      PowellMethodApache::old_handler(reason, file, line, gsl_errno);
    else
    {
      printf("GSL ERROR %s %s %d %d", reason, file, line, gsl_errno);
      abort();
    }
  }
}

PowellMethodApache::PowellMethodApache(void)
{
  old_handler = gsl_set_error_handler(handler);
}

PowellMethodApache::~PowellMethodApache(void)
{
  gsl_set_error_handler(old_handler);
}

unsigned int fcount, gcount;

double uchek_f(const gsl_vector *x, void *params)
{
  double result = 0.0;
  func_params *fnc_param = (func_params *)params;
  int n = fnc_param->n;
  std::shared_ptr<std::vector<double>> point =
    std::make_shared<std::vector<double>>(n);
  for (int i = 0; i < n; i++)
  {
    double v = gsl_vector_get(x, i);
    (*point)[i] = v;
  }
  result = fnc_param->func->value(
    point); // function value inverse because we need a maximum optimal value
  if (result != GSL_NAN)
    result = -result;
  return result;
}

//double wood_f (const gsl_vector * x, void *params)
//{
//  double u1 = gsl_vector_get(x,0);
//  double u2 = gsl_vector_get(x,1);
//  double u3 = gsl_vector_get(x,2);
//  double u4 = gsl_vector_get(x,3);
//
//  double t1 = u1 * u1 - u2;
//  double t2 = u3 * u3 - u4;
//  fcount++;
//  return 100 * t1 * t1 + (1 - u1) * (1 - u1)
//    + 90 * t2 * t2 + (1 - u3) * (1 - u3)
//    + 10.1 * ( (1 - u2) * (1 - u2) + (1 - u4) * (1 - u4) )
//    + 19.8 * (1 - u2) * (1 - u4);
//}
//
//void
//wood_initpt (gsl_vector * x)
//{
//  gsl_vector_set (x, 0, -3.0);
//  gsl_vector_set (x, 1, -1.0);
//  gsl_vector_set (x, 2, -3.0);
//  gsl_vector_set (x, 3, -1.0);
//}

std::shared_ptr<PointValue> PowellMethodApache::optimise(
  std::shared_ptr<ObjectiveFunction> func,
  std::shared_ptr<std::vector<double>> init)
{
  //gsl_ieee_env_setup();

  MultivariateFunction fn;
  fn.bestSoFar = std::make_shared<std::vector<double>>(init->size());
  fn.func = func;
  fnc_param.func = &fn;
  fnc_param.n = init->size();

  f.f = uchek_f;
  f.n = fnc_param.n;
  f.params = &fnc_param;

  const gsl_multimin_fminimizer_type *T =
    gsl_multimin_fminimizer_nmsimplex2rand; //gsl_multimin_fminimizer_nmsimplex2;
  int status;
  size_t i, iter = 0;

  gsl_vector *x = gsl_vector_alloc(f.n);
  for (i = 0; i < f.n; i++)
  {
    gsl_vector_set(x, i, (*init)[i]);
  }

  //gsl_vector_set(x, 0, 0.885982186943016);
  //gsl_vector_set(x, 1, - 2.8717911656635726);

  gsl_vector *step_size = gsl_vector_alloc(f.n);
  gsl_vector_set_all(step_size, 1.0);

  gsl_multimin_fminimizer *s = NULL;

  fcount = 0;
  gcount = 0;

  s = gsl_multimin_fminimizer_alloc(T, f.n);

  gsl_multimin_fminimizer_set(s, &f, x, step_size);

  do
  {
    iter++;
    try
    {
      status = gsl_multimin_fminimizer_iterate(s);
      double sz = gsl_multimin_fminimizer_size(s);
      status = gsl_multimin_test_size(sz, 1e-8);
    }
    catch (const char *e)
    {
      int cind_err = strcmp("gsl_multimin_fminimizer_iterate", e);
      if (cind_err != 0)
        throw e;
      iter = 100500;
      break;
    }
  } while (iter < 1000 && status == GSL_CONTINUE);

  gsl_vector *opt = gsl_multimin_fminimizer_x(s);
  point = std::make_shared<std::vector<double>>(opt->size);
  for (size_t idx = 0; idx < opt->size; idx++)
  {
    const double cur_val = gsl_vector_get(opt, idx);
    (*point)[idx] = cur_val;
  }

  //(*point)[0] = 1.1294940671047706;
  //(*point)[1] = 9.479131744735115;
  //(*point)[2] = 6.479440036899234;
  //s->fval = 57.03937701997788;

  result = std::make_shared<PointValue>(point, -s->fval);
  gsl_multimin_fminimizer_free(s);
  gsl_vector_free(x);
  gsl_vector_free(step_size);
  return result;
}

//std::shared_ptr<PointValue> PowellMethodApache::optimise(std::shared_ptr<ObjectiveFunction> func, std::shared_ptr<std::vector<double> > init)
//{
//	//gsl_ieee_env_setup();
//
//	MultivariateFunction fn;
//	fn.bestSoFar = std::make_shared<std::vector<double> >(init->size());
//	fn.func = func;
//	fnc_param.func = &fn;
//	fnc_param.n = init->size();
//
//	const int n = init->size();
//	std::vector<std::vector<double> >  direc(n);
//	for (int i = 0; i < n; i++) {
//		direc[i].resize(n);
//		direc[i][i] = 1.0;
//	}
//
//	std::vector<double> x = *init.get();
//	std::vector<double> x1 = *init.get();
//	int iter = 0;
//	double fVal = fn.func->getValueAt(init);
//	do  {
//		iter++;
//		double fX = fVal;
//		double fX2 = 0;
//		double delta = 0;
//		int bigInd = 0;
//		double alphaMin = 0;
//
//		for (int i = 0; i < n; i++) {
//			std::vector<double> d = direc[i];
//			fX2 = fVal;
//
//			PointValue optimum = search(x, d);
//			fVal = optimum.getValue();
//			alphaMin = (*optimum.getPoint())[0];
//			std::vector<std::vector<double> > result = newPointAndDirection(x, d, alphaMin);
//			x = result[0];
//
//			if ((fX2 - fVal) > delta) {
//				delta = fX2 - fVal;
//				bigInd = i;
//			}
//		}
//
//		bool stop = 2 * (fX - fVal) <=
//			(1e-8 * (abs(fX) + abs(fVal)) +
//				1e-8);
//		PointValue previous = PointValue(x1, fX);
//		PointValue current =  PointValue(x, fVal);
//
//		if (stop || iter > 1000) {
//				result = (fVal > fX) ? std::make_shared<PointValue>(current) : std::make_shared<PointValue>(previous);
//				return result;
//		}
//		std::vector<double> d(n);
//		std::vector<double> x2(n);
//		for (int i = 0; i < n; i++) {
//			d[i] = x[i] - x1[i];
//			x2[i] = 2 * x[i] - x1[i];
//		}
//
//		x1 = x;
//		fX2 = fn.func->getValueAt(std::make_shared<std::vector<double> >(x2));
//
//		if (fX > fX2) {
//			double t = 2 * (fX + fX2 - 2 * fVal);
//			double temp = fX - fVal - delta;
//			t *= temp * temp;
//			temp = fX - fX2;
//			t -= delta * temp * temp;
//
//			if (t < 0.0) {
//				PointValue optimum = search(x, d);
//				fVal = optimum.getValue();
//				alphaMin = (*optimum.getPoint())[0];
//				std::vector<std::vector<double> > result = newPointAndDirection(x, d, alphaMin);
//				x = result[0];
//
//				const int lastInd = n - 1;
//				direc[bigInd] = direc[lastInd];
//				direc[lastInd] = result[1];
//			}
//		}
//
//	} while (1);
//
//
//
//
//
//	result = std::make_shared<PointValue>(init, fVal);
//	return result;
//}

std::vector<std::vector<double>> &PowellMethodApache::newPointAndDirection(
  std::vector<double> &p,
  std::vector<double> &d,
  double optimum)
{
  const int n = (int)p.size();
  std::vector<double> nP(n);
  std::vector<double> nD(n);
  for (int i = 0; i < n; i++)
  {
    nD[i] = d[i] * optimum;
    nP[i] = p[i] + nD[i];
  }
  pointAndDirection.resize(2);
  pointAndDirection[0] = nP;
  pointAndDirection[1] = nD;
  return pointAndDirection;
}

PointValue &PowellMethodApache::search(
  std::vector<double> &startPoint,
  std::vector<double> &direction)
{
  const int n = startPoint.size();

  return srch;
}

bool PowellMethodApache::converged(
  int iteration,
  PointValue &previous,
  PointValue &current)
{
  return false;
}
