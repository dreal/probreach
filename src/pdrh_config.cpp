//
// Created by fedor on 24/02/16.
//

#include "pdrh_config.h"
#include<iostream>
#include<sstream>
#include<string.h>
#ifdef _OPENMP
    #include<omp.h>
#include <logging/easylogging++.h>

#endif
#include "version.h"

using namespace std;

pdrh_config global_config;

void parse_pdrh_config(int argc, char* argv[])
{
    // setting max number of threads
    #ifdef _OPENMP
        global_config.max_num_threads = omp_get_max_threads();
        global_config.num_threads = global_config.max_num_threads;
        omp_set_num_threads(global_config.num_threads);
    #endif
    //no arguments are input
    if(argc < 2)
    {
        print_usage();
        exit(EXIT_FAILURE);
    }
    //only one -h/--help or --version is provided
    if(argc == 2)
    {
        if((strcmp(argv[1], "-h") == 0) || (strcmp(argv[1], "--help") == 0))
        {
            print_usage();
            exit(EXIT_SUCCESS);
        }
        else if((strcmp(argv[1], "--version") == 0))
        {
            print_version();
            exit(EXIT_SUCCESS);
        }
    }
    // parsing options
    int opt_end = argc;
    //parsing ProbReach options
    for(int i = 1; i < argc; i++)
    {
        //extracting a file name
        if((strcmp(string(argv[i]).substr(string(argv[i]).find_last_of('.') + 1).c_str(), "pdrh") == 0) ||
                (strcmp(string(argv[i]).substr(string(argv[i]).find_last_of('.') + 1).c_str(), "drh") == 0))
        {
            global_config.model_filename = argv[i];
            opt_end = i;
            break;
        }
        // help
        else if((strcmp(argv[i], "-h") == 0) || (strcmp(argv[i], "--help") == 0))
        {
            print_usage();
            exit(EXIT_SUCCESS);
        }
        // probability precision
        else if(strcmp(argv[i], "-e") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> global_config.precision_prob;
            if (global_config.precision_prob <= 0)
            {
                CLOG(ERROR, "config") << "-e should be positive";
                exit(EXIT_FAILURE);
            }
        }
        // reachability depth (min = max)
        else if(strcmp(argv[i], "-k") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> global_config.reach_depth_max;
            global_config.reach_depth_min = global_config.reach_depth_max;
            if(global_config.reach_depth_max < 0)
            {
                CLOG(ERROR, "config") << "-k cannot be negative";
                exit(EXIT_FAILURE);
            }
        }
        // minimum reachability depth
        else if(strcmp(argv[i], "-l") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> global_config.reach_depth_min;
            if(global_config.reach_depth_min < 0)
            {
                CLOG(ERROR, "config") << "-l cannot be negative";
                exit(EXIT_FAILURE);
            }
            else if(global_config.reach_depth_min > global_config.reach_depth_max)
            {
                CLOG(ERROR, "config") << "Minimum reachaility depth cannot be greater than the maximum one";
                exit(EXIT_FAILURE);
            }
        }
        // maximum reachability depth
        else if(strcmp(argv[i], "-u") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> global_config.reach_depth_max;
            if(global_config.reach_depth_max < 0)
            {
                CLOG(ERROR, "config") << "-u cannot be negative";
                exit(EXIT_FAILURE);
            }
            else if(global_config.reach_depth_min > global_config.reach_depth_max)
            {
                CLOG(ERROR, "config") << "Minimum reachaility depth cannot be greater than the maximum one";
                exit(EXIT_FAILURE);
            }
        }
        // nondeterministic precision
        else if(strcmp(argv[i], "--max_nondet") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> global_config.precision_nondet;
            if(global_config.precision_nondet <= 0)
            {
                CLOG(ERROR, "config") << "--max_nondet should be positive";
                exit(EXIT_FAILURE);
            }
        }
        // precision to volume ratio
        else if(strcmp(argv[i], "--precision-ratio") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> global_config.solver_precision_ratio;
            if(global_config.solver_precision_ratio <= 0)
            {
                CLOG(ERROR, "config") << "--precision-ratio should be positive";
                exit(EXIT_FAILURE);
            }
        }
        // time series filename
        else if(strcmp(argv[i], "--series") == 0)
        {
            i++;
            global_config.series_filename = argv[i];
            istringstream is(argv[i]);
        }
        // solver binary
        else if(strcmp(argv[i], "--solver") == 0)
        {
            i++;
            global_config.solver_bin = string(argv[i]);
        }
        // time variable name
        else if(strcmp(argv[i], "--time-var") == 0)
        {
            i++;
            global_config.time_var = string(argv[i]);
        }
        // verbose
        else if(strcmp(argv[i], "--verbose") == 0)
        {
            global_config.verbose = true;
        }
        // statistical flag
        else if(strcmp(argv[i], "--sample") == 0)
        {
            global_config.sample_flag = true;
            i++;
            istringstream is(argv[i]);
            is >> global_config.sample_size;
            if(global_config.sample_size <= 0)
            {
                CLOG(ERROR, "config") << "--sample should be positive";
                exit(EXIT_FAILURE);
            }
        }
        // chernoff bound accuracy
        else if(strcmp(argv[i], "--chernoff-acc") == 0)
        {
            global_config.chernoff_flag = true;
            i++;
            istringstream is(argv[i]);
            is >> global_config.chernoff_acc;
            if (global_config.chernoff_acc <= 0)
            {
                CLOG(ERROR, "config") << "accuracy of Chernoff bound should be positive";
                exit(EXIT_FAILURE);
            }
        }
        // chernoff bound confidence
        else if(strcmp(argv[i], "--chernoff-conf") == 0)
        {
            global_config.chernoff_flag = true;
            i++;
            istringstream is(argv[i]);
            is >> global_config.chernoff_conf;
            if ((global_config.chernoff_conf < 0) ||
                    (global_config.chernoff_conf >= 1))
            {
                CLOG(ERROR, "config") << "confidence of Chernoff bound should be within [0, 1)";
                exit(EXIT_FAILURE);
            }
        }
        // bayesian accuracy
        else if(strcmp(argv[i], "--bayesian-acc") == 0)
        {
            global_config.bayesian_flag = true;
            i++;
            istringstream is(argv[i]);
            is >> global_config.bayesian_acc;
            if (global_config.bayesian_acc <= 0)
            {
                CLOG(ERROR, "config") << "accuracy for Bayesian simulations should be positive";
                exit(EXIT_FAILURE);
            }
        }
        // bayesian confidence
        else if(strcmp(argv[i], "--bayesian-conf") == 0)
        {
            global_config.bayesian_flag = true;
            i++;
            istringstream is(argv[i]);
            is >> global_config.bayesian_conf;
            if ((global_config.bayesian_conf < 0) ||
                (global_config.bayesian_conf >= 1))
            {
                CLOG(ERROR, "config") << "confidence for Bayesian simulations should be within [0, 1)";
                exit(EXIT_FAILURE);
            }
        }
        // merge flag
        else if(strcmp(argv[i], "--delta-sat") == 0)
        {
            /*
            if((!global_config.chernoff_flag) && (!global_config.bayesian_flag))
            {
                CLOG(ERROR, "config") << "flag --delta-sat can only be used with statistical model checking";
                exit(EXIT_FAILURE);
            }
            */
            global_config.delta_sat = true;
        }
        // merge flag
        else if(strcmp(argv[i], "--merge-boxes") == 0)
        {
            global_config.boxes_merge = true;
        }
        // partition continuous random parameters
        else if(strcmp(argv[i], "--partition-prob") == 0)
        {
            global_config.partition_prob = true;
        }
        // partition continuous nondeterministic parameter
        else if(strcmp(argv[i], "--partition-nondet") == 0)
        {
            global_config.partition_nondet = true;
        }
        //xml_output
        else if(strcmp(argv[i], "--xml-output") == 0)
        {
            global_config.xml_output = true;
        }
        // solution-guided
        else if(strcmp(argv[i], "--guided") == 0)
        {
            global_config.witness_guided = true;
        }
        // prepartition flag
        else if(strcmp(argv[i], "--partition") == 0)
        {
            global_config.boxes_prepartition = true;
        }
        // version
        else if(strcmp(argv[i], "--version") == 0)
        {
            print_version();
        }
        // number of threads
        else if(strcmp(argv[i], "-t") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> global_config.num_threads;
            if(global_config.num_threads <= global_config.max_num_threads)
            {
                if(global_config.num_threads > 0)
                {
                    #ifdef _OPENMP
                        omp_set_num_threads(global_config.num_threads);
                    #endif
                }
                else
                {
                    CLOG(ERROR, "config") << "Number of cores should be positive";
                    exit(EXIT_FAILURE);
                }
            }
            else
            {
                CLOG(ERROR, "config") << "Max number of cores available is " << global_config.max_num_threads << ". You specified " << global_config.num_threads;
                exit(EXIT_FAILURE);
            }
        }
        else
        {
            CLOG(ERROR, "config") << "Unrecognized option: " << argv[i];
            print_usage();
            exit(EXIT_FAILURE);
        }
    }
    // getting solver options
    stringstream s;
    for(int i = opt_end + 1; i < argc; i++)
    {
        s << argv[i] << " ";

    }
    global_config.solver_opt = s.str();
    // case if filename is not specified
    if(strcmp(global_config.model_filename.c_str(), "") == 0)
    {
        CLOG(ERROR, "config") << "Model file is not specified";
        print_usage();
        exit(EXIT_FAILURE);
    }
    CLOG_IF(global_config.verbose, INFO, "config") << "OK";
}

void print_usage()
{
    cout << endl;
    cout << "Usage:" << endl;
    cout << endl;
    cout << "	Run ./ProbReach <options> <file.pdrh/file.drh> <solver-options>" << endl;
    cout << endl;
    cout << "options:" << endl;
    cout << "	-e <double> - length of probability interval (default " << global_config.precision_prob << ")" << endl;
    cout << "	-l/--solver </path/to/solver> - full path to the solver (default " << global_config.solver_bin << ")" << endl;
    cout << "	-t <int> - number of CPU cores (default " << global_config.max_num_threads << ") (max " << global_config.max_num_threads << ")" << endl;
    cout << "	-h/--help - help message" << endl;
    cout << "	--version - version of the tool" << endl;
    cout << "	--verbose - output computation details" << endl;
    cout << endl;
}

void print_version()
{
    cout << "ProbReach " << PROBREACH_VERSION << endl;
}