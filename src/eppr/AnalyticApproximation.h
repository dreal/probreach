#ifndef ANALYTICAPPROXIMATION_H
#define ANALYTICAPPROXIMATION_H

#include <memory>
#include <vector>
class GPEP;
class ProbitRegressionPosterior;
class GpDataset;

class AnalyticApproximation {
 public:
  AnalyticApproximation(std::shared_ptr<GPEP> gp);
  ~AnalyticApproximation();

  std::shared_ptr<GPEP> gp;
  std::shared_ptr<ProbitRegressionPosterior> getValuesAt(
      std::shared_ptr<GpDataset> points);
  std::shared_ptr<ProbitRegressionPosterior> getValuesAt(
      std::shared_ptr<std::vector<std::vector<double> > > points);
};

#endif