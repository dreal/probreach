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

TEST(formal_bad_test_4, testing_bad_4_pdrh)
{
  parse_pdrh_model(
    string(PROBREACH_TEST_MODELS_DIR) + string("/bad/bad_4.pdrh"));
  // setting precision for computing the probability interval
  global_config.partition_nondet = true;
  map<string, string> partition_nondet_map = {{"n", "0.1"}};
  global_config.partition_nondet_map = partition_nondet_map;
  global_config.partition_prob = true;
  map<string, string> partition_prob_map = {{"r", "0.01"}};
  global_config.partition_prob_map = partition_prob_map;
  // computing the probability now
  map<box, capd::interval> p_map = formal::evaluate_npha(0, 0);
  // expected output
  map<box, capd::interval> expected_p_map = {
    {box("n:[-4.94066e-324,0.0625];"), capd::interval("0.757813", "1")},
    {box("n:[0.0625,0.125];"), capd::interval("0.5625", "0.773437")},
    {box("n:[0.125,0.1875];"), capd::interval("0.382813", "0.578125")},
    {box("n:[0.1875,0.25];"), capd::interval("0.25", "0.398437")},
    {box("n:[0.25,0.3125];"), capd::interval("0.132813", "0.265625")},
    {box("n:[0.3125,0.375];"), capd::interval("0.0625", "0.148437")},
    {box("n:[0.375,0.4375];"), capd::interval("0.0078125", "0.078125")},
    {box("n:[0.4375,0.5];"), capd::interval("0", "0.0234375")},
    {box("n:[0.5,0.5625];"), capd::interval("0", "0.0234375")},
    {box("n:[0.5625,0.625];"), capd::interval("0.0078125", "0.078125")},
    {box("n:[0.625,0.6875];"), capd::interval("0.0625", "0.148437")},
    {box("n:[0.6875,0.75];"), capd::interval("0.132813", "0.265625")},
    {box("n:[0.75,0.8125];"), capd::interval("0.25", "0.398437")},
    {box("n:[0.8125,0.875];"), capd::interval("0.382813", "0.578125")},
    {box("n:[0.875,0.9375];"), capd::interval("0.5625", "0.773437")},
    {box("n:[0.9375,1];"), capd::interval("0.757813", "1")},
  };
  // checking the actual p_map against the expected output
  for (auto it = p_map.cbegin(); it != p_map.cend(); it++)
  {
    EXPECT_LE(capd::intervals::width(it->first.get_map()["n"]), 0.1);
    for (auto it2 = expected_p_map.cbegin(); it2 != expected_p_map.cend();
         it2++)
    {
      if (it2->first.intersects(it->first))
      {
        capd::interval inter;
        EXPECT_TRUE(
          capd::intervals::intersection(it->second, it2->second, inter));
      }
    }
  }
}
