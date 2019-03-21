//
// Created by fedor on 13/12/18.
//

#include <iostream>
#include <cstring>
#include <sstream>
#include <fstream>
#include <logging/easylogging++.h>
#include <solver/dreal_wrapper.h>
#include "node.h"
#include "model.h"
#include "git_sha1.h"
#include "version.h"
#include "box.h"
#include "pdrh2box.h"
#include "mc.h"
#include "pdrh_config.h"
#include "decision_procedure.h"

#ifdef _OPENMP
    #include<omp.h>
#endif

extern "C"
{
    #include "pdrhparser.h"
}

INITIALIZE_EASYLOGGINGPP

extern "C" int yyparse();
extern "C" FILE *yyin;

using namespace std;
using namespace pdrh;

int main(int argc, char* argv[])
{
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
    }
    while (!feof(yyin));

    START_EASYLOGGINGPP(argc, argv);
    el::Logger* algorithm_logger = el::Loggers::getLogger("algorithm");

    // setting the model type
    pdrh::set_model_type();

    // only the following cases are supported in the formal setting
    if(pdrh::model_type == pdrh::PHA)
    {
        capd::interval probability = algorithm::evaluate_pha_bayesian(global_config.reach_depth_min, global_config.reach_depth_max,
                                                                      global_config.bayesian_acc, global_config.bayesian_conf, {});
        cout << scientific << probability << " | " << capd::intervals::width(probability) << endl;
    }
    else if(pdrh::model_type == pdrh::NPHA)
    {

        pair<box, capd::interval> probability = algorithm::evaluate_npha_cross_entropy_normal(global_config.reach_depth_min, global_config.reach_depth_max,
                                                                                          global_config.sample_size, global_config.iter_num,
                                                                                          global_config.bayesian_acc, global_config.bayesian_conf);
        cout << probability.first << " | " << probability.second << " | " << capd::intervals::width(probability.second) << endl;
    }
    else
    {
        cerr << "Unrecognised model type" << endl;
        exit(EXIT_FAILURE);
    }

    el::Loggers::unregisterLogger("algorithm");

    return 0;
}

