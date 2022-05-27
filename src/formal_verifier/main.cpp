//
// Created by fedor on 13/12/18.
//

#include <iomanip>
#include <iostream>
#include <cstring>
#include <logging/easylogging++.h>
#include "node.h"
#include "model.h"
#include "git_sha1.h"
#include "version.h"
#include "box.h"
#include "formal.h"
#include "pdrh_config.h"

#ifdef _OPENMP
    #include<omp.h>
#include <util/decision_procedure.h>

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

// the minimum depth of each path
size_t min_depth = 0;
// the maximum depth of each path
size_t max_depth = 0;
// number of point used in IVP solving
size_t num_points = 1;
// path to the input file
string in_file = "";
// minimisation flag
bool minimise_flag = false;
// half-size of the computed confidence intervals
double acc = 1e-1;
// confidence value for the computed confidence intervals
double conf = 0.95;
// number of iterations of cross-entropy algorithm
size_t num_iter = 2;
// number of sample of each iteration of cross-entropy algorithm
size_t num_samples = 10;
// number of threads
#ifdef _OPENMP
    int num_threads = omp_get_max_threads();
#else
    int num_threads = 1;
#endif


int main(int argc, char* argv[])
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
    }
    while (!feof(yyin));

    START_EASYLOGGINGPP(argc, argv);
    el::Logger* algorithm_logger = el::Loggers::getLogger("algorithm");

    // setting the model type
    pdrh::set_model_type();

    // only the following cases are supported in the formal setting
    if(pdrh::model_type == pdrh::PHA)
    {
        capd::interval probability = formal::evaluate_pha(global_config.reach_depth_min, global_config.reach_depth_max);
        cout << scientific << probability << " | " << capd::intervals::width(probability) << endl;
    }
    else if(pdrh::model_type == pdrh::NPHA)
    {
        map<box, capd::interval> probability_map = formal::evaluate_npha(global_config.reach_depth_min, global_config.reach_depth_max);
        for(auto it = probability_map.cbegin(); it != probability_map.cend(); it++)
        {
            cout << scientific << it->first << " | " << it->second << " | " << capd::intervals::width(it->second) << endl;
        }
    }
    else
    {
        int res = formal::evaluate_ha(global_config.reach_depth_min, global_config.reach_depth_max);
        switch(res)
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

    el::Loggers::unregisterLogger("algorithm");

    return 0;
}

