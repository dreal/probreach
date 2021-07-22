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
#include "qmc.h"
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

extern "C"

int yyparse();

extern "C" FILE *yyin;

using namespace std;
using namespace pdrh;

int main(int argc, char *argv[]) {
    // parse command line
    parse_pdrh_config(argc, argv);

    // opening pdrh file
    FILE *pdrhfile = fopen(global_config.model_filename.c_str(), "r");

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

    // setting the model type
    pdrh::set_model_type();

    capd::interval probability;
    if (strcmp(global_config.CI_flag, "CLT") == 0) {
        probability = algorithm::evaluate_rqmc_CLT();
    } else if (strcmp(global_config.CI_flag, "AC") == 0) {
        probability = algorithm::evaluate_rqmc_AC();
    } else if (strcmp(global_config.CI_flag, "WIL") == 0) {
        probability = algorithm::evaluate_rqmc_Will();
    } else if (strcmp(global_config.CI_flag, "LOG") == 0) {
        probability = algorithm::evaluate_rqmc_Log();
    } else if (strcmp(global_config.CI_flag, "ANS") == 0) {
        probability = algorithm::evaluate_rqmc_Ans();
    } else if (strcmp(global_config.CI_flag, "ARC") == 0) {
        probability = algorithm::evaluate_rqmc_Arc();
    } else if (strcmp(global_config.CI_flag, "QIN") == 0) {
        probability = algorithm::evaluate_Qint();
    } else if (strcmp(global_config.CI_flag, "ALL") == 0) {
        probability = algorithm::evaluate_mixCI();
    } else if (strcmp(global_config.CI_flag, "CP") == 0) {
        probability = algorithm::evaluate_rqmc_CP();
    } else
        probability = algorithm::evaluate_qmc();

    cout << scientific << probability << " | " << capd::intervals::width(probability) << endl;

    el::Loggers::unregisterLogger("algorithm");

    return 0;
}

