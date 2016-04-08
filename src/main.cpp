//
// Created by fedor on 04/03/16.
//

#include <iostream>
#include <sstream>
#include <parser/csv/csvparser.h>
#include <iomanip>
#include "pdrh_config.h"
#include "model.h"
#include "algorithm.h"
#include "easylogging++.h"
#include "rnd.h"

extern "C"
{
    #include "pdrhparser.h"
}

extern "C" int yyparse();
extern "C" FILE *yyin;

INITIALIZE_EASYLOGGINGPP

int main(int argc, char* argv[])
{
    START_EASYLOGGINGPP(argc, argv);
    el::Logger* parser_logger = el::Loggers::getLogger("parser");
    el::Logger* algorithm_logger = el::Loggers::getLogger("algorithm");
    el::Logger* solver_logger = el::Loggers::getLogger("solver");
    el::Logger* series_parser_logger = el::Loggers::getLogger("series-parser");
    el::Logger* config_parser_logger = el::Loggers::getLogger("config");
    el::Logger* rng_logger = el::Loggers::getLogger("ran_gen");

    // parse command line
    parse_pdrh_config(argc, argv);
    // setting precision on the output
    std::cout.precision(16);

    // PDRH PARSER
    CLOG_IF(global_config.verbose, INFO, "parser") << "Model file: " << global_config.model_filename;
    FILE *pdrhfile = fopen(global_config.model_filename.c_str(), "r");
    if (!pdrhfile)
    {
        CLOG(ERROR, "parser") << "Couldn't open " << global_config.model_filename;
        return -1;
    }
    std::stringstream s, pdrhnameprep;
    pdrhnameprep << global_config.model_filename << ".preprocessed";
    s << "cpp -w -P " << global_config.model_filename << " > " << pdrhnameprep.str().c_str();
    system(s.str().c_str());
    // parsing the preprocessed file
    FILE *pdrhfileprep = fopen(pdrhnameprep.str().c_str(), "r");
    // make sure it's valid:
    if (!pdrhfileprep)
    {
        CLOG(ERROR, "parser") << "Couldn't open " << pdrhnameprep;
        return -1;
    }
    // set lex to read from it instead of defaulting to STDIN:
    yyin = pdrhfileprep;
    // parse through the input until there is no more:
    do
    {
        yyparse();
    }
    while (!feof(yyin));
    std::remove(pdrhnameprep.str().c_str());
    CLOG_IF(global_config.verbose, INFO, "parser") << "OK";
    //CLOG_IF(global_config.verbose, INFO, "parser") << pdrh::model_to_string();

    switch(pdrh::model_type)
    {
        // hybrid automata
        case pdrh::HA:
        {
            decision_procedure::result res = algorithm::evaluate_ha(global_config.reach_depth_min, global_config.reach_depth_max);
            if (res == decision_procedure::SAT)
            {
                std::cout << "sat" << std::endl;
            }
            else if (res == decision_procedure::UNDET)
            {
                std::cout << "undet" << std::endl;
            }
            else if (res == decision_procedure::UNSAT)
            {
                std::cout << "unsat" << std::endl;
            }
            else if (res == decision_procedure::ERROR)
            {
                std::cout << "error" << std::endl;
                return EXIT_FAILURE;
            }
            break;
        }
        // probabilistic hybrid automata
        case pdrh::PHA:
        {
            // move this check to parser
            if(pdrh::par_map.size() > 0)
            {
                CLOG(ERROR, "algorithm") << "Found " << pdrh::par_map.size() << " nondeterministic parameters. Please specify correct model type";
                std::cout << "error" << std::endl;
                return EXIT_FAILURE;
            }
            capd::interval probability;
            if(global_config.chernoff_flag)
            {
                probability = algorithm::evaluate_pha_chernoff(global_config.reach_depth_min, global_config.reach_depth_max, global_config.chernoff_acc, global_config.chernoff_conf);
            }
            else
            {
                probability = algorithm::evaluate_pha(global_config.reach_depth_min, global_config.reach_depth_max);
            }
            std::cout << probability << std::endl;
            break;
        }
        // nondeterministic probabilistic hybrid automata
        case pdrh::NPHA:
        {
            std::map<box, capd::interval> probability_map = algorithm::evaluate_npha(global_config.reach_depth_min, global_config.reach_depth_max);
            for(auto it = probability_map.cbegin(); it != probability_map.cend(); it++)
            {
                std::cout << std::scientific << it->first << " | " << it->second << std::endl;
            }
            break;
        }
        // parameter synthesis
        case pdrh::PSY:
        {
            if(global_config.series_filename.empty())
            {
                CLOG(ERROR, "series-parser") << "Time series file is not specified";
                return EXIT_FAILURE;
            }
            std::map<std::string, std::vector<capd::interval>> time_series = csvparser::parse(global_config.series_filename);
            std::tuple<std::vector<box>, std::vector<box>, std::vector<box>> boxes = algorithm::evaluate_psy(time_series);
            std::vector<box> sat_boxes = std::get<0>(boxes);
            std::vector<box> undet_boxes = std::get<1>(boxes);
            std::vector<box> unsat_boxes = std::get<2>(boxes);
            std::cout << "sat" << std::endl;
            for(box b : sat_boxes)
            {
                std::cout << b << std::endl;
            }
            std::cout << "undet" << std::endl;
            for(box b : undet_boxes)
            {
                std::cout << b << std::endl;
            }
            std::cout << "unsat" << std::endl;
            for(box b : unsat_boxes)
            {
                std::cout << b << std::endl;
            }
            break;
        }
    }
    std::cout.precision(16);
    std::cout << std::scientific << std::setprecision(16) << capd::interval(4.9e-1) << std::endl;
    double a = 4.9e-1;
    std::cout << std::scientific << std::setprecision(16) << capd::interval(a) << std::endl;
    double b = atof(std::string("4.9e-1").c_str());
    std::cout << std::scientific << std::setprecision(16) << capd::interval(b) << std::endl;
    std::cout << std::scientific << std::setprecision(16) << capd::interval("4.9e-1", "4.9e-1") << std::endl;
    return EXIT_SUCCESS;
}