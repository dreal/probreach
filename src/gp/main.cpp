#include <stdio.h>
//#include <crtdbg.h>
//#include <Windows.h>
#include <capd/intervals/lib.h>
#include <gsl/gsl_cdf.h>
#include <gsl/gsl_qrng.h>
#include <gsl/gsl_rng.h>
#include <logging/easylogging++.h>
#include <solver/dreal_wrapper.h>

#include <cstring>
#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <vector>

#include "AnalyticApproximation.h"
#include "GpDataset.h"
#include "ProbitRegressionPosterior.h"
#include "SmmcOptions.h"
#include "SmoothedModelCheker.h"
#include "box.h"
#include "git_sha1.h"
#include "mc.h"
#include "model.h"
#include "naive.h"
#include "node.h"
#include "pdrh2box.h"
#include "pdrh_config.h"
#include "version.h"
//#include "algorithm.h"
#include <chrono>
#include <iomanip>

#include "easylogging++.h"
#include "pdrh_config.h"
#include "qmc.h"
#include "rnd.h"
//#include "stability.h"
#include <omp.h>

#include <chrono>
#include <ctime>
#include <iostream>

#include "DebugLogMatrix.h"

using namespace std;
std::ofstream myfile("test.csv");

extern "C" {
#include "pdrhparser.h"
}

INITIALIZE_EASYLOGGINGPP

extern "C" int yyparse();
extern "C" FILE *yyin;

using namespace std;
using namespace pdrh;

// the minimum depth of each path
size_t min_depth = 0;
// the maximum depth of each path
size_t max_depth = 0;
// number of points
size_t num_points = 1;
// path to the input file
string in_file = "";
// minimisation flag
// bool minimise_flag = false;
// half-size of the computed confidence intervals
// double acc = 1e-1;
// confidence value for the computed confidence intervals
double conf = 0.95;
// number of iterations of cross-entropy algorithm
// size_t num_iter = 2;
// number of sample of each iteration of cross-entropy algorithm
size_t num_samples = 10;

// printing help message
void print_help() {
  cout << "Usage:" << endl;
  cout << endl;
  cout << "	simulate <options> <file.pdrh/file.drh> <solver-options>"
       << endl;
  cout << endl;
  cout << "options:" << endl;
  cout << "-h - displays help message" << endl;
  cout << "-v - prints out the current version of ProbReach" << endl;
  cout << "-l - minimum depth of every simulation path (default = " << min_depth
       << ")" << endl;
  cout << "-u - maximum depth of every simulation path (default = " << max_depth
       << ")" << endl;
  cout << "-n - number of points (default = " << num_points << ")" << endl;
  // cout << "--min - minimise reachability probability (default = " <<
  // minimise_flag << ")" << endl; cout << "--acc - half-size of the computed
  // confidence intervals (default = " << acc << ")" << endl;
  cout << "--conf - confidence value for the computed confidence intervals "
          "(default = "
       << conf << ")" << endl;
  // cout << "--iter - confidence value for the computed confidence intervals
  // (default = " << num_iter << ")" << endl;
  cout << "--samples - number of samples for each iteration of cross-entropy "
          "algorithm (default = "
       << num_samples << ")" << endl;
  cout << "--solver - full path to the solver executable (default = "
       << dreal::solver_bin << ")" << endl;
}

// parsing command line options
void parse_cmd(int argc, char *argv[]) {
  // parsing ProbReach options
  for (int i = 1; i < argc; i++) {
    // filename
    if (string(argv[i]).substr(string(argv[i]).find_last_of('.') + 1) ==
            "pdrh" ||
        string(argv[i]).substr(string(argv[i]).find_last_of('.') + 1) ==
            "drh") {
      in_file = argv[i];
    }
    // help
    else if (string(argv[i]) == "-h") {
      print_help();
      exit(EXIT_SUCCESS);
    }
    // version
    else if (string(argv[i]) == "-v") {
      cout << "ProbReach " << PROBREACH_VERSION << " (" << git::get_sha1()
           << ")" << endl;
      exit(EXIT_SUCCESS);
    }
    // minimum path length
    else if (string(argv[i]) == "-l") {
      i++;
      istringstream is(argv[i]);
      is >> min_depth;
      if (min_depth < 0) {
        cerr << "-l must be positive and not larger than -u";
        exit(EXIT_FAILURE);
      }
    }
    // maximum path length
    else if (string(argv[i]) == "-u") {
      i++;
      istringstream is(argv[i]);
      is >> max_depth;
      if (max_depth < 0) {
        cerr << "-u must be positive and not smaller than -l";
        exit(EXIT_FAILURE);
      }
    }
    // maximum number of points
    else if (string(argv[i]) == "-n") {
      i++;
      istringstream is(argv[i]);
      is >> num_points;
      if (num_points < 0) {
        cerr << "-n must be positive";
        exit(EXIT_FAILURE);
      }
    }
    // confidence
    else if ((strcmp(argv[i], "--conf") == 0)) {
      i++;
      istringstream is(argv[i]);
      is >> conf;
      if (conf <= 0 || conf >= 1) {
        cerr << "--conf must be a number from (0,1) interval";
        exit(EXIT_FAILURE);
      }
    }
    // number of samples per iteration of cross-entropy algorithm
    else if ((strcmp(argv[i], "--samples") == 0)) {
      i++;
      istringstream is(argv[i]);
      is >> num_samples;
      if (num_samples <= 0) {
        cerr << "--samples must be positive";
        exit(EXIT_FAILURE);
      }
    } else if (string(argv[i]) == "--solver") {
      i++;
      dreal::solver_bin = string(argv[i]);
    }
  }
  // checking if the input file is specified
  if (in_file == "") {
    cerr << "Input file has not been specified" << endl;
    exit(EXIT_FAILURE);
  }
}

int main(int argc, char *argv[]) {
  parse_cmd(argc, argv);
  // opening pdrh file
  FILE *pdrhfile = fopen(in_file.c_str(), "r");
  if (!pdrhfile) {
    cerr << "Couldn't open the file: " << endl;
    exit(EXIT_FAILURE);
  }
  // set lex to read from it instead of defaulting to STDIN:
  yyin = pdrhfile;
  // parse through the input until there is no more:
  do {
    yyparse();
  } while (!feof(yyin));

  START_EASYLOGGINGPP(argc, argv);
  el::Logger *algorithm_logger = el::Loggers::getLogger("algorithm");

  global_config.verbose_result = true;
  global_config.verbose = true;
  // global_config.bayesian_flag = true;
  // omp_set_num_threads(1);

  cout << "num_samples: " << num_samples << endl;
  cout << "num_points: " << num_points << endl;
  cout << "conf: " << conf << endl;

  // the main algorithm is here

  //--------------Evaluation----------------
  auto start = std::chrono::system_clock::now();
  vector<vector<pdrh::mode *>> paths =
      pdrh::get_all_paths(min_depth, max_depth);
  double ressat2 = 0, resunsat2 = 0;
  // double result = 0;

  CLOG_IF(global_config.verbose, INFO, "algorithm") << endl
                                                    << "SIMPLE GP ALGORITHM";

  // initialize mu generator
  gsl_qrng *m = gsl_qrng_alloc(gsl_qrng_sobol,
                               static_cast<unsigned int>(pdrh::par_map.size()));
  // getting domain of mu parameterS
  int NondetParCount = pdrh::par_map.size();
  cout << "NondetParCount" << NondetParCount << endl;
  box mu_domain = pdrh2box::get_nondet_domain();
  CLOG_IF(global_config.verbose, INFO, "algorithm")
      << "Nondet_domain = " << mu_domain;

  // initialize  random generator
  const gsl_rng_type *TT;
  gsl_rng *rr;
  gsl_rng_env_setup();
  TT = gsl_rng_default;
  rr = gsl_rng_alloc(TT);

  int NondetP = num_points;  // number of points of Nondet Parameter
  int pointsarray[NondetP];  // Nondet points array
  double Carray[NondetP];    // center probability
  double Sats[NondetP];      // N_s number
  double points = 0;
  int Total_samples = num_samples;             // Total samples number
  double NonDPoints[NondetP][NondetParCount];  // Nondet points values;
  double SATnum = 0;
  double sat2 = 0, unsat2 = 0, undet2 = 0;

  map<string, capd::interval> one_map;
  for (auto &it : pdrh::rv_map) {
    one_map.insert(make_pair(it.first, capd::interval(1, 1)));
  }
  box box_one = box(one_map);

  // main loop
  for (int l = 0; l < NondetP; l++) {
    CLOG_IF(global_config.verbose, INFO, "algorithm")
        << endl
        << "Nondet count============" << l;
    sat2 = 0, unsat2 = 0, undet2 = 0;
    double CI = 0;
    points = 1;
    double conf = global_config.qmc_conf;
    double Ca = gsl_cdf_gaussian_Pinv(1 - (1 - conf) / 2, 1);
    // initialize Nondet sample
    box mu_sample = rnd::get_sobol_sample(m, mu_domain);
    CLOG_IF(global_config.verbose, INFO, "algorithm")
        << "Nondet_sample = " << mu_sample;  // n
    vector<double> vect;
    rnd::func(vect, mu_sample);

    for (int h = 0; h < NondetParCount; h++) {
      NonDPoints[l][h] = vect[h];
      cout << "NonDPoints[l][" << h << "]" << NonDPoints[l][h] << endl;
    }
    //  cout<<"NonDPoints[l][0]"<<NonDPoints[l][0]<<endl;
    //  cout<<"NonDPoints[l][1]"<<NonDPoints[l][1]<<endl;

    // initialize Sobol generator
    gsl_qrng *q2 = gsl_qrng_alloc(
        gsl_qrng_sobol, static_cast<unsigned int>(pdrh::rv_map.size()));
    // getting domain of random parameters
    map<string, capd::interval> sobol_domain_map2;
    for (auto &it : pdrh::rv_map) {
      sobol_domain_map2.insert(make_pair(it.first, capd::interval(0, 1)));
    }
    box sobol_domain2(sobol_domain_map2);
    gsl_rng_set(rr, static_cast<unsigned long>(l));

    // change to Random
    const gsl_rng_type *Ti;
    gsl_rng *ri;
    gsl_rng_env_setup();
    Ti = gsl_rng_default;
    // creating random generator
    ri = gsl_rng_alloc(Ti);
    // setting the seed
    gsl_rng_set(ri, std::chrono::system_clock::now().time_since_epoch() /
                        std::chrono::milliseconds(1));

#pragma omp parallel for
    for (size_t i = 0; i < Total_samples; i++) {
      box sobol_sample;
      box R_sample;  // change to Random //!!!!!!!!!!!!!!!1
#pragma omp critical
      {
        sobol_sample = rnd::get_sobol_sample(q2, sobol_domain2);
        //   double non=4; //const of nondet mu param //!!!!!!!!!!!!!!!1
        //   //R_sample = rnd::get_random_sample2(ri, mu_sample, NondetParCount,
        //   non);      //!!!!!!!!!!!!!!!1
        //    R_sample = rnd::get_random_sample(ri); //!!!!!!!!!!!!!!!1
        //    CLOG_IF(global_config.verbose, INFO, "algorithm") << "R SAMPLE :"
        //    <<R_sample;   //!!!!!!!!!!!!!!!1
      }
      // sample from [x1_min,x1_max]*...*[xn_min,xn_max] after applying icdf
      box GPicdf_sample;

#pragma omp critical
      {
        GPicdf_sample = rnd::get_GPicdf(sobol_sample, mu_sample);
        CLOG_IF(global_config.verbose, INFO, "algorithm")
            << "GPicdf_sample :" << GPicdf_sample;
      }

      int res = decision_procedure::evaluate(paths, {GPicdf_sample, mu_sample},
                                             dreal::solver_bin, "");
// int res = decision_procedure::evaluate(paths, {R_sample, mu_sample},
// dreal::solver_bin, "");            //!!!!!!!!!!!!!!!1
// computing value of indicator function
#pragma omp critical
      {
        switch (res) {
          // hybrid automata
          case decision_procedure::SAT: {
            sat2++;
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
            break;
          }
          case decision_procedure::UNSAT: {
            unsat2++;
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
            break;
          }
          case decision_procedure::UNDET: {
            undet2++;
            CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "UNDET";
            break;
          }
          default:
            break;
        }
        CLOG_IF(global_config.verbose, INFO, "algorithm")
            << "Number of SAT: " << sat2;
        CLOG_IF(global_config.verbose, INFO, "algorithm")
            << "Number of UNSAT: " << unsat2;
        CLOG_IF(global_config.verbose, INFO, "algorithm")
            << "Number of UNDET: " << undet2;

        ressat2 = sat2 / points;
        resunsat2 = (points - unsat2) / points;
        SATnum = sat2;

        points++;
      }
    }
    points = points - 1;
    cout << "Sat NUM [" << l << "]: " << SATnum << endl;
    Sats[l] = SATnum;
    pointsarray[l] = points;
    Carray[l] = resunsat2;  // - global_config.qmc_acc/2 + result;
    // CLOG_IF(global_config.verbose, INFO, "algorithm") <<
    // "global_config.qmc_acc/2===" << global_config.qmc_acc / 2;
  }

  double Ca = gsl_cdf_gaussian_Pinv(
      1 - (1 - conf) / 2,
      1);  //- REPLACE BETA !!!!!!!!!!!!!************************************
  cout << "Ca=" << Ca << endl;
  //--------------Evaluation----------------

  //--------------CP----------------
  cout << "C-P approach" << endl;
  double UParray[NondetP];
  double LOarray[NondetP];
  // cout << "global_config.qmc_acc/2=" <<global_config.qmc_acc/2<< endl;
  for (int l = 0; l < NondetP; l++) {
    if (Sats[l] == 0) {
      LOarray[l] = 0;
      UParray[l] = gsl_cdf_beta_Pinv(1 - ((1 - conf) / 2), Sats[l] + 1,
                                     Total_samples - Sats[l]);
    } else if (Sats[l] == Total_samples) {
      LOarray[l] = gsl_cdf_beta_Pinv((1 - conf) / 2, Sats[l],
                                     Total_samples - Sats[l] + 1);
      UParray[l] = 1;
    } else {
      LOarray[l] = gsl_cdf_beta_Pinv((1 - conf) / 2, Sats[l],
                                     Total_samples - Sats[l] + 1);
      UParray[l] = gsl_cdf_beta_Pinv(1 - ((1 - conf) / 2), Sats[l] + 1,
                                     Total_samples - Sats[l]);
    }
  }

  if (NondetParCount == 2) {
    // write data to the "test.csv" file
    myfile << "Non-det pont"
           << ";"
           << "NOND Sigma value"
           << ";"
           << "NOND Mu value"
           << ";"
           << "CPLower"
           << ";"
           << "CPUpper"
           << ";"
           << "CPCenter"
           << ";"
           << "GPLower"
           << ";"
           << "GPUpper"
           << ";"
           << "GPCenter" << std::endl;
    for (int l = 0; l < NondetP; l++) {
      CLOG_IF(global_config.verbose, INFO, "algorithm")
          << l << "-MU points=" << pointsarray[l]
          << "   NOND Sigma value=" << NonDPoints[l][0]
          << "   NOND Mu value=" << NonDPoints[l][1] << " SATS=" << Sats[l]
          << " CPLower=" << LOarray[l] << " CPUpper=" << UParray[l]
          << " CPCenter=" << Carray[l];
      myfile << l << ";" << NonDPoints[l][0] << ";" << NonDPoints[l][1] << ";"
             << LOarray[l] << ";" << UParray[l] << ";" << Carray[l]
             << std::endl;
    }
  } else if (NondetParCount == 1) {
    // write data to the "test.csv" file
    myfile << "Non-det pont"
           << ";"
           << "NONDvalue"
           << ";"
           << "CPLower"
           << ";"
           << "CPUpper"
           << ";"
           << "CPCenter"
           << ";"
           << "GPLower"
           << ";"
           << "GPUpper"
           << ";"
           << "GPCenter" << std::endl;
    for (int l = 0; l < NondetP; l++) {
      CLOG_IF(global_config.verbose, INFO, "algorithm")
          << l << "-MU points=" << pointsarray[l]
          << "   NONDvalue=" << NonDPoints[l][0] << " SATS=" << Sats[l]
          << " CPLower=" << LOarray[l] << " CPUpper=" << UParray[l]
          << " CPCenter=" << Carray[l];
      myfile << l << ";" << NonDPoints[l][0] << ";" << LOarray[l] << ";"
             << UParray[l] << ";" << Carray[l] << std::endl;
    }
  }
  cout << "C-P approach end" << endl;

  //--------------CP----------------

  //--------------GP----------------
  double beta = Ca;
  const int ncolumns =
      NondetParCount;  // Dimention of nondet parameters (1 or 2)
  double x_points[NondetP][ncolumns];
  double y_points[NondetP];
  double xt_points[NondetP][ncolumns];

  for (int l = 0; l < NondetP; l++) {
    y_points[l] = Carray[l];
    // xt_points[l][ncolumns - 1] = NonDPoints[l + 1];
    // x_points[l][ncolumns - 1] = NonDPoints[l + 1];
  }
  for (int l = 0; l < NondetP; l++) {
    for (int h = 0; h < ncolumns; h++) {
      xt_points[l][h] = NonDPoints[l][h];
      x_points[l][h] = NonDPoints[l][h];
    }
  }

  cout << "x_points" << endl;
  for (int l = 0; l < NondetP; l++) {
    for (int h = 0; h < ncolumns; h++) {
      cout << "{" << x_points[l][h] << "}"
           << ", ";
    }
    cout << endl;
  }
  cout << "y_points" << endl;
  for (int l = 0; l < NondetP; l++) {
    cout << y_points[l] << endl;
  }
  cout << "xt_points" << endl;
  for (int l = 0; l < NondetP; l++) {
    for (int h = 0; h < ncolumns; h++) {
      cout << "{" << xt_points[l][h] << "}"
           << ", ";
    }
    cout << endl;
  }

  vector<vector<double>> x(1), *xt;
  vector<double> y;
  x.resize(sizeof(x_points) / sizeof(x_points[0]));
  y.resize(sizeof(y_points) / sizeof(y_points[0]));
  xt = new std::vector<std::vector<double>>();
  xt->resize(sizeof(xt_points) / sizeof(xt_points[0]));
  for (size_t i = 0; i < x.size(); i++) {
    x[i].resize(ncolumns);
    for (size_t j = 0; j < ncolumns; j++) {
      x[i][j] = x_points[i][j];
    }
  };
  for (size_t i = 0; i < xt->size(); i++) {
    (*xt)[i].resize(ncolumns);
    for (size_t j = 0; j < ncolumns; j++) {
      (*xt)[i][j] = xt_points[i][j];
    }
  };
  copy(&y_points[0], &y_points[y.size()], y.begin());

  shared_ptr<GpDataset> dataset = make_shared<GpDataset>(x, y);
  shared_ptr<SmmcOptions> options = make_shared<SmmcOptions>(ncolumns + 1);
  shared_ptr<SmoothedModelCheker> mc = make_shared<SmoothedModelCheker>();
  std::vector<std::shared_ptr<Parameter>> params;
  shared_ptr<AnalyticApproximation> approx =
      mc->getAnalyticApproximation(dataset, params, options);
  std::shared_ptr<std::vector<std::vector<double>>> ptr_xt(xt);
  shared_ptr<ProbitRegressionPosterior> result = approx->getValuesAt(ptr_xt);
  DebugLogMatrix::printMatrix("getClassProbabilities", __LINE__,
                              result->getClassProbabilities());
  DebugLogMatrix::printMatrix("getLowerBound(beta)", __LINE__,
                              result->getLowerBound(beta));
  DebugLogMatrix::printMatrix("getUpperBound(beta)", __LINE__,
                              result->getUpperBound(beta));
  //--------------GP----------------
  auto end = std::chrono::system_clock::now();
  std::chrono::duration<double> elapsed_seconds = end - start;
  std::time_t end_time = std::chrono::system_clock::to_time_t(end);
  std::cout << "finished computation at " << std::ctime(&end_time)
            << "elapsed time: " << elapsed_seconds.count() << "s\n";
  return 0;
}
