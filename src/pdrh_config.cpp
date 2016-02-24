//
// Created by fedor on 24/02/16.
//

#include "pdrh_config.h"
#include<iostream>
#include<sstream>
#include<string.h>
#ifdef _OPENMP
    #include<omp.h>
#endif
#include "version.h"

using namespace std;
pdrh_config parse_pdrh_config(int argc, char* argv[])
{
    pdrh_config config;
    // setting max number of threads
    #ifdef _OPENMP
        config.max_num_threads = omp_get_max_threads();
        config.num_threads = config.max_num_threads;
        omp_set_num_threads(config.num_threads);
    #endif
    //no arguments are input
    if(argc < 2)
    {
        print_usage(config);
        exit(EXIT_FAILURE);
    }
    //only one -h/--help or --version is provided
    if(argc == 2)
    {
        if((strcmp(argv[1], "-h") == 0) || (strcmp(argv[1], "--help") == 0))
        {
            print_usage(config);
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
            config.model_filename = argv[i];
            opt_end = i;
            break;
        }
        // help
        else if((strcmp(argv[i], "-h") == 0) || (strcmp(argv[i], "--help") == 0))
        {
            print_usage(config);
            exit(EXIT_SUCCESS);
        }
        // probability precision
        else if(strcmp(argv[i], "-e") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> config.precision_prob;
            if (config.precision_prob <= 0)
            {
                cerr << "-e should be positive" << endl;
                exit(EXIT_FAILURE);
            }
        }
        // reachability depth (min = max)
        else if(strcmp(argv[i], "-k") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> config.reach_depth_max;
            config.reach_depth_min = config.reach_depth_max;
            if(config.reach_depth_max < 0)
            {
                cerr << "-k cannot be negative" << endl;
                exit(EXIT_FAILURE);
            }
        }
        // minimum reachability depth
        else if(strcmp(argv[i], "-l") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> config.reach_depth_min;
            if(config.reach_depth_min < 0)
            {
                cerr << "-l cannot be negative" << endl;
                exit(EXIT_FAILURE);
            }
            else if(config.reach_depth_min > config.reach_depth_max)
            {
                cerr << "minimum reachaility depth cannot be greater than the maximum one" << endl;
                exit(EXIT_FAILURE);
            }
        }
        // maximum reachability depth
        else if(strcmp(argv[i], "-u") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> config.reach_depth_max;
            if(config.reach_depth_max < 0)
            {
                cerr << "-u cannot be negative" << endl;
                exit(EXIT_FAILURE);
            }
            else if(config.reach_depth_min > config.reach_depth_max)
            {
                cerr << "minimum reachaility depth cannot be greater than the maximum one" << endl;
                exit(EXIT_FAILURE);
            }
        }
        // nondeterministic precision
        else if(strcmp(argv[i], "--max_nondet") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> config.precision_nondet;
            if(config.precision_nondet <= 0)
            {
                cerr << "--max_nondet should be positive" << endl;
                exit(EXIT_FAILURE);
            }
        }
        // time series filename
        else if(strcmp(argv[i], "--series") == 0)
        {
            i++;
            config.series_filename = argv[i];
            istringstream is(argv[i]);
        }
        // solver binary
        else if(strcmp(argv[i], "--solver") == 0)
        {
            i++;
            config.solver_bin = string(argv[i]);
        }
        // verbose
        else if(strcmp(argv[i], "--verbose") == 0)
        {
            config.verbose = true;
        }
        // merge flag
        else if(strcmp(argv[i], "--merge-boxes") == 0)
        {
            config.boxes_merge = true;
        }
        //xml_output
        else if(strcmp(argv[i], "--xml-output") == 0)
        {
            config.xml_output = true;
        }
        // solution-guided
        else if(strcmp(argv[i], "--guided") == 0)
        {
            config.witness_guided = true;
        }
        // prepartition flag
        else if(strcmp(argv[i], "--partition") == 0)
        {
            config.boxes_prepartition = true;
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
            is >> config.num_threads;
            if(config.num_threads <= config.max_num_threads)
            {
                if(config.num_threads > 0)
                {
                    #ifdef _OPENMP
                        omp_set_num_threads(config.num_threads);
                    #endif
                }
                else
                {
                    cerr << "Number of cores should be positive" << endl;
                    exit(EXIT_FAILURE);
                }
            }
            else
            {
                cerr << "Max number of cores available is " << config.max_num_threads << ". You specified " << config.num_threads << endl;
                exit(EXIT_FAILURE);
            }
        }
        else
        {
            cerr << "Unrecognized option: " << argv[i] << endl;
            print_usage(config);
            exit(EXIT_FAILURE);
        }
    }
    // getting solver options
    stringstream s;
    for(int i = opt_end + 1; i < argc; i++)
    {
        s << argv[i] << " ";

    }
    config.solver_opt = s.str();
    // case if filename is not specified
    if(strcmp(config.model_filename.c_str(), "") == 0)
    {
        cerr << "model file is not specified" << endl;
        print_usage(config);
        exit(EXIT_FAILURE);
    }
    return config;
}

void print_usage(pdrh_config config)
{
    cout << endl;
    cout << "Usage:" << endl;
    cout << endl;
    cout << "	Run ./ProbReach <options> <file.pdrh/file.drh> <solver-options>" << endl;
    cout << endl;
    cout << "options:" << endl;
    cout << "	-e <double> - length of probability interval (default " << config.precision_prob << ")" << endl;
    cout << "	-l/--solver </path/to/solver> - full path to the solver (default " << config.solver_bin << ")" << endl;
    cout << "	-t <int> - number of CPU cores (default " << config.max_num_threads << ") (max " << config.max_num_threads << ")" << endl;
    cout << "	-h/--help - help message" << endl;
    cout << "	--version - version of the tool" << endl;
    cout << "	--verbose - output computation details" << endl;
    cout << endl;
}

void print_version()
{
    cout << "ProbReach " << PROBREACH_VERSION << endl;
}