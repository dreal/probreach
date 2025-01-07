//
// Created by fedor on 13/12/18.
//

#include <iomanip>
#include <iostream>
#include <cstring>
#include <sstream>
#include <fstream>
#include <solver/dreal_wrapper.h>
#include "node.h"
#include "model.h"
#include "git_sha1.h"
#include "version.h"
#include "box.h"
#include "pdrh2box.h"
#include "formal.h"
#include "pdrh_config.h"

#ifdef _OPENMP
#include <omp.h>
#include <util/decision_procedure.h>
#endif

extern "C"
{
#include "pdrhparser.h"
}

extern "C" int yyparse();
extern "C" FILE *yyin;

using namespace std;
using namespace pdrh;



int main(int argc, char *argv[])
{
  // setting precision for the output to 16 digits
  cout << setprecision(16);
  // parse command line
  parse_pdrh_config(argc, argv);

  // opening pdrh file
  FILE *pdrhfile = fopen(global_config.model_filename.c_str(), "r");
  if (!pdrhfile)
  {
    cerr << "Couldn't open the file: " << endl;
    exit(EXIT_FAILURE);
  }
  // set lex to read from it instead of defaulting to STDIN:
  yyin = pdrhfile;
  // parse through the input until there is no more:
  do
  {
    yyparse();
  } while (!feof(yyin));

  // setting the model type
  pdrh::set_model_type();

  // only the following cases are supported in the formal setting
  if (pdrh::model_type == pdrh::PHA)
  {
    capd::interval probability = formal::evaluate_pha(
      global_config.reach_depth_min, global_config.reach_depth_max);
    cout << scientific << probability << " | "
         << capd::intervals::width(probability) << endl;
  }
  else if (pdrh::model_type == pdrh::NPHA)
  {
    map<box, capd::interval> probability_map;
    if(global_config.upper_p_bound_flag)
    {
      probability_map = formal::evaluate_npha_upper_bound(
        global_config.reach_depth_min, global_config.reach_depth_max);
    }
    else
    {
      probability_map = formal::evaluate_npha(
        global_config.reach_depth_min, global_config.reach_depth_max);
    }
    // outputting the probability map
    for (auto it = probability_map.cbegin(); it != probability_map.cend(); it++)
    {
      cout << scientific << it->first << " | " << it->second << " | "
           << capd::intervals::width(it->second) << endl;
    }
  }
  else
  {
    int res = formal::evaluate_ha(
      global_config.reach_depth_min, global_config.reach_depth_max);
    switch (res)
    {
    case decision_procedure::result::SAT:
      cout << "sat" << endl;
      break;

    case decision_procedure::result::UNSAT:
      cout << "unsat" << endl;
      break;

    case decision_procedure::result::UNDET:
      cout << "undet" << endl;
      break;

    default:
      cerr << "Unrecognised verification result" << endl;
      exit(EXIT_FAILURE);
    }
  }

  return 0;
}
