#include "AnalyticApproximation.h"

#include "GPEP.h"
#include "GpDataset.h"

AnalyticApproximation::AnalyticApproximation(std::shared_ptr<GPEP> gp) {
  this->gp = gp;
}

AnalyticApproximation::~AnalyticApproximation() {}

std::shared_ptr<ProbitRegressionPosterior> AnalyticApproximation::getValuesAt(
    std::shared_ptr<GpDataset> points) {
  return gp->getGpPosterior(points);
  ;
}

std::shared_ptr<ProbitRegressionPosterior> AnalyticApproximation::getValuesAt(
    std::shared_ptr<std::vector<std::vector<double> > > points) {
  std::shared_ptr<GpDataset> testSet =
      std::make_shared<GpDataset>(*points.get());
  return gp->getGpPosterior(testSet);
}