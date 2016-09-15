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
#include <easylogging++.h>

#include "version.h"
#include "model.h"

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
        if(is_pdrh(argv[i]) || is_drh(argv[i]))
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
        else if((strcmp(argv[i], "-e") == 0) || (strcmp(argv[i], "--precision-prob") == 0))
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
        // sample size
        else if(strcmp(argv[i], "--sample-size") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> global_config.sample_size;
            if(global_config.sample_size <= 0)
            {
                CLOG(ERROR, "config") << "--sample-size must be positive";
                exit(EXIT_FAILURE);
            }
        }
        // elite ration
        else if(strcmp(argv[i], "--elite-ratio") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> global_config.elite_ratio;
            if(global_config.elite_ratio <= 0 || global_config.elite_ratio >= 1)
            {
                CLOG(ERROR, "config") << "--elite-ratio must be a number in the interval (0,1)";
                exit(EXIT_FAILURE);
            }
        }
        // sobol sequence optimization bound
        else if(strcmp(argv[i], "--sobol-term-arg") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> global_config.sobol_term_arg;
            if(global_config.sobol_term_arg <= 0)
            {
                CLOG(ERROR, "config") << "--sobol-term-arg must be positive";
                exit(EXIT_FAILURE);
            }
        }
        // cross-entropy termination condition
        else if(strcmp(argv[i], "--cross-entropy-term-arg") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> global_config.cross_entropy_term_arg;
            if(global_config.cross_entropy_term_arg <= 0)
            {
                CLOG(ERROR, "config") << "--cross-entropy-term-arg must be positive";
                exit(EXIT_FAILURE);
            }
        }
        // minimum probability flag
        else if(strcmp(argv[i], "--min-prob") == 0)
        {
            global_config.min_prob = true;
            global_config.max_prob = false;
        }
        // cross entropy normal flag
        else if(strcmp(argv[i], "--cross-entropy-beta") == 0)
        {
            global_config.cross_entropy_beta = true;
            global_config.cross_entropy_normal = false;
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
                CLOG(ERROR, "config") << "Minimum reachaility depth cannot be descending than the maximum one";
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
                CLOG(ERROR, "config") << "Minimum reachaility depth cannot be descending than the maximum one";
                exit(EXIT_FAILURE);
            }
        }
        // nondeterministic precision
        else if(strcmp(argv[i], "--precision-nondet") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> global_config.precision_nondet;
            if(global_config.precision_nondet <= 0)
            {
                CLOG(ERROR, "config") << "--max-nondet should be positive";
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
        // integral pdf step
        else if(strcmp(argv[i], "--integral-pdf-step") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> global_config.integral_pdf_step;
            if(global_config.integral_pdf_step <= 0)
            {
                CLOG(ERROR, "config") << "--integral-pdf-step should be positive";
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
        else if(strcmp(argv[i], "--time-var-name") == 0)
        {
            i++;
            global_config.time_var_name = string(argv[i]);
        }
        // chernoff bound accuracy
        else if(strcmp(argv[i], "--chernoff-acc") == 0)
        {
            global_config.chernoff_flag = true;
            global_config.stat_flag = true;
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
            global_config.stat_flag = true;
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
            global_config.stat_flag = true;
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
            global_config.stat_flag = true;
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
            i++;
            bool map_end = false;
            while(!map_end)
            {
                if(is_flag(argv[i]) || is_drh(argv[i]) || is_pdrh(argv[i]))
                {
                    map_end = true;
                    i--;
                }
                else
                {
                    istringstream var_is(argv[i]);
                    string var = var_is.str();
                    i++;
                    if(is_flag(argv[i]) || is_drh(argv[i]) || is_pdrh(argv[i]))
                    {
                        CLOG(ERROR, "config") << "partition precision for variable \"" << var << "\" is not defined";
                        exit(EXIT_FAILURE);
                    }
                    else
                    {
                        istringstream val_is(argv[i]);
                        pdrh::push_prob_partition_prec(var, capd::interval(val_is.str(), val_is.str()));
                        i++;
                    }
                }
            }
        }
        // partition continuous nondeterministic parameter
        else if(strcmp(argv[i], "--partition-nondet") == 0)
        {
            global_config.partition_nondet = true;
            i++;
            bool map_end = false;
            while(!map_end)
            {
                if(is_flag(argv[i]) || is_drh(argv[i]) || is_pdrh(argv[i]))
                {
                    map_end = true;
                    i--;
                }
                else
                {
                    istringstream var_is(argv[i]);
                    string var = var_is.str();
                    i++;
                    if(is_flag(argv[i]) || is_drh(argv[i]) || is_pdrh(argv[i]))
                    {
                        CLOG(ERROR, "config") << "partition precision for variable \"" << var << "\" is not defined";
                        exit(EXIT_FAILURE);
                    }
                    else
                    {
                        istringstream val_is(argv[i]);
                        pdrh::push_nondet_partition_prec(var, capd::interval(val_is.str(), val_is.str()));
                        i++;
                    }
                }
            }
        }
        // partition the synthesized parameters
        else if(strcmp(argv[i], "--partition-psy") == 0)
        {
            global_config.partition_psy = true;
        }
        // xml_output
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
        // verbose
        else if(strcmp(argv[i], "--verbose") == 0)
        {
            global_config.verbose = true;
            global_config.verbose_result = true;
        }
        // sobol
        else if(strcmp(argv[i], "--sobol") == 0)
        {
            global_config.sobol_flag = true;
            global_config.cross_entropy_flag = false;
        }
        // cross-entropy
        else if(strcmp(argv[i], "--cross-entropy") == 0)
        {
            global_config.cross_entropy_flag = true;
            global_config.sobol_flag = false;
        }
        // sample size display
        else if(strcmp(argv[i], "--verbose-result") == 0)
        {
            global_config.verbose_result = true;
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
    cout << "	ProbReach <options> <file.pdrh/file.drh> <solver-options>" << endl;
    cout << endl;
    cout << "options:" << endl;
    cout << "--bayesian-acc <double> - half-length of the confidence interval in Bayesian estimations (default " << global_config.bayesian_acc << ")" << endl;
    cout << "--bayesian-conf <double> - confidence value in Bayesian estimations (default " << global_config.bayesian_conf << ")" << endl;
    cout << "--chernoff-acc <double> - half-length of the confidence interval in Chernoff-Hoeffding method (default " << global_config.chernoff_acc << ")" << endl;
    cout << "--chernoff-conf <double> - confidence value in Chernoff-Hoeffding method (default " << global_config.chernoff_conf << ")" << endl;
    cout << "--delta-sat - uses the delta-sat answer of the solver only (statistical model checking and habrid automata only; default false)" << endl;
    cout << "-e/--precision-prob <double> - length of probability interval (default " << global_config.precision_prob << ")" << endl;
    cout << "-h/--help - help message" << endl;
    cout << "--integral-inf-coeff <double> - ratio for the continuous random variables with unbounded support (default " << global_config.integral_inf_coeff << ")" << endl;
    cout << "--integral-pdf-step <double> - step value used for bounding domains of continuous random variables with user-defined distributions (default " << global_config.integral_pdf_step << ")" << endl;
    cout << "-k <double> - reachability depth bound (default: the shortest path length if exists)" << endl;
    cout << "-l <double> - lower reachability depth bound (cannot be used without -u; default: the shortest path length if exists)" << endl;
    cout << "--merge-boxes - merges boxes which were partitioned during parameter synthesis (default false)" << endl;
    cout << "--partition-nondet - partitions the domain nondeterministic parameters up to the precision --precision-nondet (default false)" << endl;
    cout << "--partition-prob - obtains a partition of the domain continuous random parameters satisfying -e/--precision-prob (default false)" << endl;
    cout << "--partition-psy - partitions the domain the synthesized parameters up to the precision defined in the time series data (default false)" << endl;
    cout << "--precision-nondet - length of the largest dimension of nondeterministic box (default " << global_config.precision_nondet << ")" << endl;
    cout << "--precision-ratio <double> - solver precision ratio defined as (solver-precision = min-box-dimension * precision-ratio) (default " << global_config.solver_precision_ratio << ")" << endl;
    cout << "--series </path/to/solver> - full path to the solver (default " << global_config.solver_bin << ")" << endl;
    cout << "--solver <path> - name of the file containing the time series data" << endl;
    cout << "-t <int> - number of CPU cores (default " << global_config.max_num_threads << ") (max " << global_config.max_num_threads << ")" << endl;
    cout << "--time-var-name <string> - the name of the variable representing time in the model (default tau)" << endl;
    cout << "-u <double> - upper reachability depth bound (cannot be used without -l; default: the shortest path length if exists)" << endl;
    cout << "--verbose - output computation details (default false)" << endl;
    cout << "--verbose-result - outputs the runtime and the number of samples (statistical model checking only; default false)" << endl;
    cout << "--version - version of the tool" << endl;
    cout << endl;
}

void print_version()
{
    cout << "ProbReach " << PROBREACH_VERSION << endl;
}

bool is_flag(char* str)
{
    return (str[0] == '-') && (str[1] == '-');
}

bool is_pdrh(char* str)
{
    return strcmp(string(str).substr(string(str).find_last_of('.') + 1).c_str(), "pdrh") == 0;
}

bool is_drh(char* str)
{
    return strcmp(string(str).substr(string(str).find_last_of('.') + 1).c_str(), "drh") == 0;
}