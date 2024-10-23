#include <gtest/gtest.h>
#include <iostream>

#include "formal.h"
#include "pdrh_config.h"
#include "node.h"
#include "model.h"
#include "git_sha1.h"
#include "version.h"
#include "box.h"
#include "pdrh2box.h"
#include "decision_procedure.h"
#include "solver/dreal_wrapper.h"
#include "test_env.h"

#ifdef _OPENMP
#include <omp.h>
#endif

extern "C"
{
#include "pdrhparser.h"
}

extern "C" int yyparse();
extern "C" FILE *yyin;

using namespace std;

static void parse_pdrh_model(string filepath)
{
  // opening the model file
  FILE *pdrhfile = fopen(filepath.c_str(), "r");
  if (!pdrhfile)
  {
    cerr << "Couldn't open the file: " << filepath << endl;
    exit(EXIT_FAILURE);
  }
  // set lex to read from it instead of defaulting to STDIN:
  yyin = pdrhfile;
  // parse through the input until there is no more:
  do
  {
    yyparse();
  } while (!feof(yyin));
}

TEST(formal_good_test_1, testing_good_1_pdrh)
{
  parse_pdrh_model(
    string(PROBREACH_TEST_MODELS_DIR) +
    string("/cars/car_stopping_nonlinear_1.pdrh"));
  // setting precision for computing the probability interval
  global_config.precision_prob = 5e-2;
  global_config.partition_prob = true;
  // computing the probability now
  capd::interval probability = formal::evaluate_pha(3, 3);
  EXPECT_LE(capd::intervals::width(probability), global_config.precision_prob);
  EXPECT_TRUE(capd::interval("0.01", "0.09").contains(probability));
}
