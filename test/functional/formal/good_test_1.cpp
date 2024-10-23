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
    string(PROBREACH_TEST_MODELS_DIR) + string("/good/good_1.pdrh"));
  // setting precision for computing the probability interval
  global_config.precision_prob = 1e-3;
  // computing the probability now
  capd::interval probability = formal::evaluate_pha(0, 0);
  // true probability in this example is 0.1; so the probability interval:
  // 1) must contain 0.1
  // 2) its width must be <= "global_config.precision_prob"
  EXPECT_TRUE(probability.contains(capd::interval("0.1", "0.1")));
  EXPECT_LE(capd::intervals::width(probability), global_config.precision_prob);
}
