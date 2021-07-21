#define _USE_MATH_DEFINES

#include "GPEP.h"

#include <gsl/gsl_sf_erf.h>

#include <cmath>

#include "CavGauss.h"
#include "DebugLogMatrix.h"
#include "DoubleMatrix.h"
#include "EPupdate.h"
#include "Gauss.h"
#include "GpDataset.h"
#include "GpPosterior.h"
#include "IAlgebra.h"
#include "IMatrix.h"
#include "KernelFunction.h"
#include "MatrixGSL.h"
#include "ProbitRegressionPosterior.h"

double GPEP::CORRECTION_FACTOR = 1;
const double GPEP::sqrt2 = sqrt(2.0);
const double GPEP::invSqrt2 = 1.0 / sqrt2;
const double GPEP::log_2 = log(2.0);

GPEP::GPEP(std::shared_ptr<KernelFunction> kernel) : AbstractGP(kernel) {
  logdet_LC = 0;
  eps_damp = 0.5;
  scale = 1;
  covarianceCorrection = 1e-4;
}

GPEP::~GPEP() {}

double GPEP::erf(double x) {
  // TODO: Add your implementation code here.
  return gsl_sf_erf(x);
}

// std::shared_ptr<KernelFunction> GPEP::getKernel(void)
//{
//	return kernelFunction;
//}
//
//
// std::shared_ptr<GpDataset> GPEP::getTrainingSet(void)
//{
//	return trainingSet;
//}
//
//
// void GPEP::setTrainingSet(std::shared_ptr<GpDataset> trainingSet)
//{
//	this->trainingSet = trainingSet;
//}

void GPEP::setScale(int scale) { this->scale = scale; }

int GPEP::getScale(void) { return scale; }

void GPEP::setCovarianceCorrection(double covarianceCorrection) {
  this->covarianceCorrection = covarianceCorrection;
}

void GPEP::doTraining(void) {
  std::shared_ptr<Gauss> gauss = expectationPropagation(1e-6);

  std::shared_ptr<IMatrix> v_tilde = gauss->Term->getColumn(0);
  std::shared_ptr<IMatrix> tau_tilde = gauss->Term->getColumn(1);

  std::shared_ptr<IMatrix> diagSigma_tilde =
      algebra->createZeros(tau_tilde->getLength(), 1);
  for (int i = 0; i < diagSigma_tilde->getLength(); i++)
    diagSigma_tilde->put(i, 1.0 / tau_tilde->get(i));
  mu_tilde = v_tilde->mul(diagSigma_tilde);
  std::shared_ptr<IMatrix> Sigma_tilde =
      algebra->createDiag(diagSigma_tilde->getData());

  invC = algebra->solvePositive(gauss->C->add(Sigma_tilde),
                                algebra->createEye(mu_tilde->getLength()));
}

std::shared_ptr<Gauss> GPEP::expectationPropagation(double tolerance) {
  double sum;
  gauss = std::make_shared<Gauss>();
  const int n = trainingSet->getSize();

  gauss->C = algebra->createMatrix(
      *(trainingSet->calculateCovariances(getKernel()).get()));

  double CORRECTION = covarianceCorrection;
  for (int i = 0; i < gauss->C->getRows(); i++)
    gauss->C->put(i, i, gauss->C->get(i, i) + CORRECTION);

  //		DebugLogMatrix::printMatrix("expectationPropagation:gauss->C",
  //__LINE__, ((MatrixGSL*)gauss->C.get())->matrixObject->matrix);
  gauss->LC_t = algebra->cholesky(gauss->C);
  //		DebugLogMatrix::printMatrix("expectationPropagation:gauss->LC_t",
  //__LINE__, ((MatrixGSL*)gauss->LC_t.get())->matrixObject->matrix);
  gauss->LC = gauss->LC_t->transpose();
  //		DebugLogMatrix::printMatrix("expectationPropagation:gauss->LC",
  //__LINE__, ((MatrixGSL*)gauss->LC.get())->matrixObject->matrix);

  sum = 0;
  std::shared_ptr<IMatrix> gauss_LC_diag = gauss->LC->diag();
  for (int i = 0; i < gauss_LC_diag->getLength(); i++)
    sum += log(gauss_LC_diag->get(i));
  logdet_LC = 2 * sum;
  double logZprior = 0.5 * (logdet_LC);

  std::shared_ptr<IMatrix> logZterms = algebra->createZeros(n, 1);
  std::shared_ptr<IMatrix> logZloo = algebra->createZeros(n, 1);
  std::shared_ptr<IMatrix> Term = algebra->createZeros(n, 2);
  computeMarginalMoments(gauss, Term);

  // Stuff related to the likelihood
  gauss->LikPar_p =
      algebra->createMatrix(trainingSet->getTargets())->mul(scale);
  gauss->LikPar_q = algebra->createOnes(n, 1)->mul(scale)->sub(gauss->LikPar_p);
  const int NODES = 96;
  gauss->xGauss = algebra->createZeros(NODES, 1);
  gauss->wGauss = algebra->createZeros(NODES, 1);
  gausshermite(NODES, gauss->xGauss, gauss->wGauss);
  //		DebugLogMatrix::printMatrix("expectationPropagation:gauss->xGauss",
  //__LINE__, ((MatrixGSL*)gauss->xGauss.get())->matrixObject->matrix);
  //		DebugLogMatrix::printMatrix("expectationPropagation:gauss->wGauss",
  //__LINE__, ((MatrixGSL*)gauss->wGauss.get())->matrixObject->matrix);
  gauss->logwGauss = algebra->createZeros(gauss->wGauss->getLength(), 1);
  for (int i = 0; i < gauss->logwGauss->getLength(); i++)
    gauss->logwGauss->put(i, log(gauss->wGauss->get(i)));

  // initialize cycle control
  int MaxIter = 1000;
  double tol = tolerance;
  double logZold = 0;
  double logZ = 2 * tol;
  int steps = 0;

  double logZappx = 0;
  while ((std::abs(logZ - logZold) > tol) & (steps < MaxIter)) {
    // cycle control
    steps = steps + 1;
    logZold = logZ;

    // TO DO cavGauss Отличается в Java [2]	0.015725000000000006 в реализации
    // 0.031673909223419554
    std::shared_ptr<CavGauss> cavGauss = ComputeCavities(gauss, Term->neg());

    // [Term,logZterms,logZloo] = EPupdate(cavGauss,gauss.LikFunc,y,
    // Term, eps_damp);
    std::shared_ptr<EPupdate> update =
        ep_update(cavGauss, Term, eps_damp, NULL, gauss->LikPar_p,
                  gauss->LikPar_q, gauss->xGauss, gauss->logwGauss);
    Term = update->TermNew;
    logZterms = update->logZterms;
    logZloo = update->logZ;

    //			DebugLogMatrix::printMatrix("expectationPropagation:Term", __LINE__,
    //((MatrixGSL*)Term.get())->matrixObject->matrix);
    //			DebugLogMatrix::printMatrix("expectationPropagation:logZterms",
    //__LINE__, ((MatrixGSL*)logZterms.get())->matrixObject->matrix);
    //			DebugLogMatrix::printMatrix("expectationPropagation:logZloo",
    //__LINE__, ((MatrixGSL*)logZloo.get())->matrixObject->matrix);

    logZappx = computeMarginalMoments(gauss, Term);
    logZ = logZterms->sum() + logZappx;
    //			DebugLogMatrix::printMatrix("expectationPropagation:logZappx",
    //__LINE__, logZappx);
    //			DebugLogMatrix::printMatrix("expectationPropagation:logZ", __LINE__,
    //logZ);
  }

  // finishing up
  logZ = logZ - logZprior;
  gauss->logZloo = logZloo->sum();
  gauss->logZappx = logZappx;
  gauss->logZterms = logZterms;
  gauss->logZ = logZ;
  gauss->Term = Term;

  // pi = normcdf(Gauss.m./sqrt(1+Gauss.diagV));

  return gauss;
}

double GPEP::computeMarginalMoments(std::shared_ptr<Gauss> gauss,
                                    std::shared_ptr<IMatrix> Term) {
  double sum;
  double logZappx;
  const int N = Term->getRows();
  std::shared_ptr<IMatrix> tmp;

  //		DebugLogMatrix::printMatrix("computeMarginalMoments:Term", __LINE__,
  //((MatrixGSL*)Term.get())->matrixObject->matrix);

  // (repmat(Term(:,2),1,N).*Gauss.LC)
  tmp = Term->getColumn(1)->repmat(1, N)->mul(gauss->LC);
  //		DebugLogMatrix::printMatrix("computeMarginalMoments:tmp", __LINE__,
  //((MatrixGSL*)tmp.get())->matrixObject->matrix);
  std::shared_ptr<IMatrix> A = gauss->LC_t->mmul(tmp)->add(
      algebra->createEye(N)->mul(CORRECTION_FACTOR));
  //		DebugLogMatrix::printMatrix("computeMarginalMoments:A", __LINE__,
  //((MatrixGSL*)A.get())->matrixObject->matrix);

  // Serious numerical stability issue with the calculation
  // of A (i.e. A = LC' * tmp + I)
  // as it does not appear to be PD for large amplitudes
  gauss->L = algebra->cholesky(A)->transpose();
  //		DebugLogMatrix::printMatrix("computeMarginalMoments:L", __LINE__,
  //((MatrixGSL*)gauss->L.get())->matrixObject->matrix);
  //

  // Gauss.W = Gauss.L\(Gauss.LC');
  gauss->W = algebra->solve(gauss->L, gauss->LC_t);
  //		DebugLogMatrix::printMatrix("computeMarginalMoments:W", __LINE__,
  //((MatrixGSL*)gauss->W.get())->matrixObject->matrix);

  // Gauss.diagV = sum(Gauss.W.*Gauss.W,1)';
  tmp = gauss->W->mul(gauss->W);
  //		DebugLogMatrix::printMatrix("computeMarginalMoments:tmp", __LINE__,
  //((MatrixGSL*)tmp.get())->matrixObject->matrix);
  gauss->diagV = algebra->createZeros(N, 1);
  for (int i = 0; i < N; i++) gauss->diagV->put(i, tmp->getColumn(i)->sum());
  //		DebugLogMatrix::printMatrix("computeMarginalMoments:gauss->diagV",
  //__LINE__, ((MatrixGSL*)gauss->diagV.get())->matrixObject->matrix);

  // or
  // gauss.diagV = gauss.W.transpose().mmul(gauss.W).diag();

  // Gauss.m = Gauss.W'*(Gauss.W*Term(:,1));
  tmp = gauss->W->mmul(Term->getColumn(0));
  //		DebugLogMatrix::printMatrix("computeMarginalMoments:tmp", __LINE__,
  //((MatrixGSL*)tmp.get())->matrixObject->matrix);

  gauss->m = gauss->W->transpose()->mmul(tmp);

  // logdet = -2*sum(log(diag(Gauss.L))) + 2*sum(log(diag(Gauss.LC)));
  double logdet = 0;
  sum = 0;
  tmp = gauss->L->diag();
  for (int i = 0; i < tmp->getLength(); i++) sum += log(tmp->get(i));
  logdet += -2 * sum;

  // sum = 0;
  // tmp = gauss.LC.diag();
  // for (int i = 0; i < tmp.getLength(); i++)
  // sum += Math.log(tmp.get(i));

  logdet += logdet_LC;
  //		DebugLogMatrix::printMatrix("computeMarginalMoments:logdet",
  //__LINE__, logdet);

  // logZappx = 0.5*(Gauss.m'*Term(:,1) + logdet);
  logZappx = 0.5 * (gauss->m->transpose()->dot(Term->getColumn(0)) + logdet);
  //		DebugLogMatrix::printMatrix("computeMarginalMoments:logZappx",
  //__LINE__, logZappx);

  return logZappx;
}

void GPEP::gausshermite(int n, std::shared_ptr<IMatrix> x,
                        std::shared_ptr<IMatrix> w) {
  std::shared_ptr<IMatrix> x0 = algebra->createZeros(x->getLength(), 1);
  std::shared_ptr<IMatrix> w0 = algebra->createZeros(w->getLength(), 1);
  int m = (n + 1) / 2;
  double z = 0, pp = 0, p1 = 0, p2 = 0, p3 = 0;
  for (int i = 0; i < m; i++) {
    if (i == 0)
      z = sqrt(2.0 * (double)n + 1.0) -
          1.85575 * pow(2.0 * (double)n + 1.0, -0.16667);
    else if (i == 1)
      z = z - 1.14 * pow((double)n, 0.426) / z;
    else if (i == 2)
      z = 1.86 * z - 0.86 * x0->get(0);
    else if (i == 3)
      z = 1.91 * z - 0.91 * x0->get(1);
    else
      z = 2.0 * z - x0->get(i - 2);

    for (int its = 0; its < 10; its++) {
      p1 = 1.0 / sqrt(sqrt(M_PI));
      p2 = 0.0;
      for (double j = 1; j <= n; j++) {
        p3 = p2;
        p2 = p1;
        const double a = z * sqrt(2.0 / (double)j) * p2;
        const double b = sqrt((j - 1) / j) * p3;
        p1 = a - b;
        //				System.currentTimeMillis();
      }
      pp = sqrt(2.0 * (double)n) * p2;
      double z1 = z;
      z = z1 - p1 / pp;
      if (std::abs(z - z1) < 2.2204e-16) break;
    }

    x0->put(i, z);
    x0->put(n - 1 - i, -z);          // x(n+1-i) = -z;
    w0->put(i, 2 / (pp * pp));       // w(i) = 2/(pp*pp);
    w0->put(n - 1 - i, w0->get(i));  // w(n+1-i) = w(i);
  }

  w0 = w0->div(sqrt(M_PI));  // w = w/sqrt(pi);
  x0 = x0->mul(sqrt(2.0));
  x0 = x0->sort();  // x = sort(x);
  x->copy(x0);
  w->copy(w0);
}

std::shared_ptr<CavGauss> GPEP::ComputeCavities(std::shared_ptr<Gauss> gauss,
                                                std::shared_ptr<IMatrix> Term) {
  //	DebugLogMatrix::printMatrix("ComputeCavities:Term", __LINE__,
  //((MatrixGSL*)Term.get())->matrixObject->matrix);
  std::shared_ptr<CavGauss> cavGauss = std::make_shared<CavGauss>();

  // C = Gauss.diagV;
  //	DebugLogMatrix::printMatrix("ComputeCavities:diagV", __LINE__,
  //((MatrixGSL*)gauss->diagV.get())->matrixObject->matrix);
  std::shared_ptr<IMatrix> C(gauss->diagV);

  // s = 1./(1 + Term(:,2).*C);
  std::shared_ptr<IMatrix> s = algebra->createOnes(C->getLength(), 1)
                                   ->div(Term->getColumn(1)->mul(C)->add(1));
  //	DebugLogMatrix::printMatrix("ComputeCavities:s", __LINE__,
  //((MatrixGSL*)s.get())->matrixObject->matrix);

  // CavGauss.diagV = s.*C;
  cavGauss->diagV = s->mul(C);
  //	DebugLogMatrix::printMatrix("ComputeCavities:CavGauss.diagV", __LINE__,
  //((MatrixGSL*)cavGauss->diagV.get())->matrixObject->matrix);

  // CavGauss.m = s.*(Gauss.m + Term(:,1).*C);
  cavGauss->m = s->mul(gauss->m->add(Term->getColumn(0)->mul(C)));
  //	DebugLogMatrix::printMatrix("ComputeCavities:CavGauss.m", __LINE__,
  //((MatrixGSL*)cavGauss->m.get())->matrixObject->matrix);

  return cavGauss;
}

std::shared_ptr<EPupdate> GPEP::ep_update(std::shared_ptr<CavGauss> cavGauss,
                                          std::shared_ptr<IMatrix> Term,
                                          double eps_damp, void* LogLikFunc,
                                          std::shared_ptr<IMatrix> LikPar_p,
                                          std::shared_ptr<IMatrix> LikPar_q,
                                          std::shared_ptr<IMatrix> xGauss,
                                          std::shared_ptr<IMatrix> wGauss) {
  std::shared_ptr<EPupdate> update = std::make_shared<EPupdate>();

  std::shared_ptr<IMatrix> Cumul =
      algebra->createZeros(LikPar_p->getLength(), 2);
  std::shared_ptr<IMatrix> logZ = GaussHermiteNQ(
      LikPar_p, LikPar_q, cavGauss->m, cavGauss->diagV, xGauss, wGauss, Cumul);

  //	DebugLogMatrix::printMatrix("ep_update:Cumul", __LINE__,
  //((MatrixGSL*)Cumul.get())->matrixObject->matrix);
  //	DebugLogMatrix::printMatrix("ep_update:logZ", __LINE__,
  //((MatrixGSL*)logZ.get())->matrixObject->matrix);

  update->logZ = logZ;

  std::shared_ptr<IMatrix> m2 =
      algebra->createZeros(cavGauss->m->getLength(), 1);
  for (int i = 0; i < m2->getLength(); i++)
    m2->put(i, cavGauss->m->get(i) * cavGauss->m->get(i));
  //	DebugLogMatrix::printMatrix("ep_update:m2", __LINE__,
  //((MatrixGSL*)m2.get())->matrixObject->matrix);
  std::shared_ptr<IMatrix> logV =
      algebra->createZeros(cavGauss->m->getLength(), 1);
  for (int i = 0; i < logV->getLength(); i++)
    logV->put(i, log(cavGauss->diagV->get(i)));
  //	DebugLogMatrix::printMatrix("ep_update:logV", __LINE__,
  //((MatrixGSL*)logV.get())->matrixObject->matrix);

  std::shared_ptr<IMatrix> cumul1 =
      algebra->createZeros(cavGauss->m->getLength(), 1);
  for (int i = 0; i < cumul1->getLength(); i++)
    cumul1->put(i, Cumul->getColumn(0)->get(i) * Cumul->getColumn(0)->get(i));

  std::shared_ptr<IMatrix> cumul2 =
      algebra->createZeros(cavGauss->m->getLength(), 1);
  for (int i = 0; i < cumul2->getLength(); i++)
    cumul2->put(i, log(Cumul->getColumn(1)->get(i)));

  //	DebugLogMatrix::printMatrix("ep_update:cumul1", __LINE__,
  //((MatrixGSL*)cumul1.get())->matrixObject->matrix);
  //	DebugLogMatrix::printMatrix("ep_update:cumul2", __LINE__,
  //((MatrixGSL*)cumul2.get())->matrixObject->matrix);
  // logZterms = logZ ...
  // + 0.5*( (CavGauss.m.^2./CavGauss.diagV + log(CavGauss.diagV)) -
  // (Cumul(:,1).^2./Cumul(:,2) + log(Cumul(:,2))));

  std::shared_ptr<IMatrix> tmp =
      m2->div(cavGauss->diagV)
          ->add(logV)
          ->sub(cumul1->div(Cumul->getColumn(1))->add(cumul2));
  update->logZterms = logZ->add(tmp->mul(0.5));

  //	DebugLogMatrix::printMatrix("ep_update:tmp", __LINE__,
  //((MatrixGSL*)tmp.get())->matrixObject->matrix);

  // TermNew = [
  // Cumul(:,1)./Cumul(:,2) - CavGauss.m./CavGauss.diagV,
  // 1./Cumul(:,2) - 1./CavGauss.diagV
  // ];

  std::shared_ptr<IMatrix> ones = algebra->createOnes(LikPar_p->getLength(), 1);
  std::shared_ptr<IMatrix> TermNew =
      algebra->createZeros(LikPar_p->getLength(), 2);
  std::shared_ptr<IMatrix> c1 = Cumul->getColumn(0)
                                    ->div(Cumul->getColumn(1))
                                    ->sub(cavGauss->m->div(cavGauss->diagV));
  std::shared_ptr<IMatrix> c2 =
      ones->div(Cumul->getColumn(1))->sub(ones->div(cavGauss->diagV));

  //	DebugLogMatrix::printMatrix("ep_update:c1", __LINE__,
  //((MatrixGSL*)c1.get())->matrixObject->matrix);
  //	DebugLogMatrix::printMatrix("ep_update:c2", __LINE__,
  //((MatrixGSL*)c2.get())->matrixObject->matrix);

  TermNew->putColumn(0, c1);
  TermNew->putColumn(1, c2);

  // TermNew = (1-eps_damp)*Term + eps_damp*TermNew;
  TermNew = Term->mul(1 - eps_damp)->add(TermNew->mul(eps_damp));
  //	DebugLogMatrix::printMatrix("ep_update:TermNew", __LINE__,
  //((MatrixGSL*)TermNew.get())->matrixObject->matrix);
  update->TermNew = TermNew;
  return update;
}

std::shared_ptr<IMatrix> GPEP::GaussHermiteNQ(
    std::shared_ptr<IMatrix> FuncPar_p, std::shared_ptr<IMatrix> FuncPar_q,
    std::shared_ptr<IMatrix> m, std::shared_ptr<IMatrix> v,
    std::shared_ptr<IMatrix> xGH, std::shared_ptr<IMatrix> logwGH,
    std::shared_ptr<IMatrix> Cumul) {
  std::shared_ptr<IMatrix> stdv = algebra->createZeros(v->getLength(), 1);
  for (int i = 0; i < stdv->getLength(); i++) stdv->put(i, sqrt(v->get(i)));

  int Nnodes = xGH->getLength();
  std::shared_ptr<IMatrix> tmp;

  // tmp = bsxfun(@times,stdv,xGH(:)')
  tmp = stdv->mmul(xGH->transpose());
  // Y = bsxfun(@plus, tmp, m(:));
  std::shared_ptr<IMatrix> Y = tmp->add(m->repmat(1, Nnodes));

  // tmp = feval(FuncName, Y, FuncPar);
  tmp = logprobitpow(Y, FuncPar_p, FuncPar_q);
  // G = bsxfun(@plus, tmp, logwGH(:)');
  std::shared_ptr<IMatrix> G =
      tmp->add(logwGH->transpose()->repmat(tmp->getRows(), 1));

  // maxG = max(G,[],2);
  std::shared_ptr<IMatrix> maxG = algebra->createZeros(G->getRows(), 1);
  for (int i = 0; i < G->getRows(); i++) maxG->put(i, G->getRow(i)->max());

  // G = G-repmat(maxG,1,Nnodes);
  // expG = exp(G);
  G = G->sub(maxG->repmat(1, Nnodes));
  std::shared_ptr<IMatrix> expG =
      algebra->createZeros(G->getRows(), G->getColumns());
  for (int i = 0; i < expG->getLength(); i++) expG->put(i, exp(G->get(i)));

  // denominator = sum(expG,2);
  // logZ = maxG + log(denominator);
  std::shared_ptr<IMatrix> denominator =
      algebra->createZeros(expG->getRows(), 1);
  std::shared_ptr<IMatrix> logdenominator =
      algebra->createZeros(expG->getRows(), 1);
  for (int i = 0; i < expG->getRows(); i++)
    denominator->put(i, expG->getRow(i)->sum());
  for (int i = 0; i < denominator->getLength(); i++)
    logdenominator->put(i, log(denominator->get(i)));
  std::shared_ptr<IMatrix> logZ = maxG->add(logdenominator);

  // deltam = stdv.*(expG*xGH(:))./denominator;
  std::shared_ptr<IMatrix> deltam =
      stdv->mul(expG->mmul(xGH))->div(denominator);

  // Cumul(:,1) = m + deltam;
  Cumul->putColumn(0, m->add(deltam));

  // Cumul(:,2) = v.*(expG*xGH(:).^2)./denominator - deltam.^2;
  std::shared_ptr<IMatrix> xGH2 =
      algebra->createZeros(xGH->getRows(), xGH->getColumns());
  for (int i = 0; i < xGH2->getLength(); i++)
    xGH2->put(i, xGH->get(i) * xGH->get(i));

  std::shared_ptr<IMatrix> deltam2 =
      algebra->createZeros(deltam->getRows(), deltam->getColumns());
  for (int i = 0; i < deltam2->getLength(); i++)
    deltam2->put(i, deltam->get(i) * deltam->get(i));

  Cumul->putColumn(1, v->mul(expG->mmul(xGH2))->div(denominator)->sub(deltam2));

  return logZ;
}

std::shared_ptr<IMatrix> GPEP::logprobitpow(std::shared_ptr<IMatrix> X,
                                            std::shared_ptr<IMatrix> LikPar_p,
                                            std::shared_ptr<IMatrix> LikPar_q) {
  const int m = X->getColumns();
  std::shared_ptr<IMatrix> Y =
      algebra->createZeros(X->getRows(), X->getColumns());

  for (int i = 0; i < Y->getLength(); i++) Y->put(i, ncdflogbc(X->get(i)));
  std::shared_ptr<IMatrix> Za = Y->mul(LikPar_p->repmat(1, m));
  // Za = ncdflogbc(X).mul(LikPar_p.repmat(1, m));

  for (int i = 0; i < Y->getLength(); i++) Y->put(i, ncdflogbc(-X->get(i)));
  std::shared_ptr<IMatrix> Zb = Y->mul(LikPar_q->repmat(1, m));
  // Zb = ncdflogbc(X.neg()).mul(LikPar_q.repmat(1, m));

  return Za->add(Zb);
}

double GPEP::ncdflogbc(double x) {
  const double treshold = -sqrt2 * 5.0;
  const double z = -x;
  if (x >= 0) return log(1.0 + erf(x * invSqrt2)) - log_2;
  if (treshold < x)  // (treshold < x && x < 0)
    return log(1 - erf(-x * invSqrt2)) - log_2;
  // (x <= treshold)
  return -0.5 * log(M_PI) - log_2 - 0.5 * z * z - log(z) +
         log(1 - 1 / z + 3 / pow(z, 4) - 15 / pow(z, 6) + 105 / pow(z, 8) -
             945 / pow(z, 10));
}

std::shared_ptr<ProbitRegressionPosterior> GPEP::getGpPosterior(
    std::shared_ptr<GpDataset> testSet) {
  std::shared_ptr<std::vector<double> > mmK =
      testSet->calculateVariances(getKernel());
  //	DebugLogMatrix::printMatrix("getGpPosterior:mmk", __LINE__, mmK);
  std::shared_ptr<std::vector<std::vector<double> > > mnK =
      testSet->calculateCovariances(getKernel(), trainingSet);
  //	DebugLogMatrix::printMatrix("getGpPosterior:mnk", __LINE__, mnK);
  std::shared_ptr<IMatrix> ks = algebra->createMatrix(*mnK.get());
  std::shared_ptr<IMatrix> kss = algebra->createMatrix(*mmK.get());

  if (invC == nullptr || mu_tilde == nullptr || trainingSet->isModified())
    doTraining();
  std::shared_ptr<IMatrix> tmp = ks->mmul(invC);
  //	DebugLogMatrix::printMatrix("getGpPosterior:tmp", __LINE__,
  //((MatrixGSL*)tmp.get())->matrixObject->matrix);
  std::shared_ptr<IMatrix> fs = tmp->mmul(mu_tilde);
  //	DebugLogMatrix::printMatrix("getGpPosterior:fs", __LINE__,
  //((MatrixGSL*)fs.get())->matrixObject->matrix);
  std::shared_ptr<IMatrix> vfs = kss->sub(tmp->mmul(ks->transpose())->diag());
  //	DebugLogMatrix::printMatrix("getGpPosterior:vfs", __LINE__,
  //((MatrixGSL*)vfs.get())->matrixObject->matrix);
  sp_data1 = std::make_shared<std::vector<double> >(fs->getData());
  sp_data2 = std::make_shared<std::vector<double> >(vfs->getData());
  sp_posterior =
      std::make_shared<ProbitRegressionPosterior>(testSet, sp_data1, sp_data2);
  return sp_posterior;
}

double GPEP::getMarginalLikelihood() {
  std::shared_ptr<Gauss> gauss = expectationPropagation(1e-3);
  return gauss->logZ;
}

std::shared_ptr<std::vector<double> > GPEP::getMarginalLikelihoodGradient() {
  throw "not implemented";
  return std::shared_ptr<std::vector<double> >();
}
