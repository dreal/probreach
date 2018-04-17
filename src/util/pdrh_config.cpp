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
#include "pdrh.h"
#include "git_sha1.h"

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
        else if((strcmp(argv[i], "-e") == 0))
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
//            else if(global_config.reach_depth_min > global_config.reach_depth_max)
//            {
//                CLOG(ERROR, "config") << "Minimum reachaility depth cannot be smaller than the maximum one";
//                exit(EXIT_FAILURE);
//            }
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
//            else if(global_config.reach_depth_min > global_config.reach_depth_max)
//            {
//                CLOG(ERROR, "config") << "Minimum reachaility depth cannot be smaller than the maximum one";
//                exit(EXIT_FAILURE);
//            }
        }
        // nondeterministic precision
        else if(strcmp(argv[i], "--precision-nondet") == 0)
        {
            //global_config.partition_nondet = true;
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
            global_config.solver_type = solver::detect_solver(global_config.solver_bin);
        }
        // solver binary
        else if(strcmp(argv[i], "--secondary-solver") == 0)
        {
            i++;
            global_config.secondary_solver_bin = string(argv[i]);
            global_config.secondary_solver_type = solver::detect_solver(global_config.secondary_solver_bin);
        }
        // time variable name
        else if(strcmp(argv[i], "--time-var-name") == 0)
        {
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
                    if(find(global_config.time_var_name.begin(), global_config.time_var_name.end(), argv[i]) == global_config.time_var_name.end())
                    {
                        global_config.time_var_name.push_back(argv[i]);
                    }
                    i++;
                }
            }
        }
        // controller plan output
        else if(strcmp(argv[i], "--controller-plant-output") == 0)
        {
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
                    if(find(global_config.controller.plant_output.begin(), global_config.controller.plant_output.end(), argv[i]) == global_config.controller.plant_output.end())
                    {
                        global_config.controller.plant_output.push_back(argv[i]);
                    }
                    i++;
                }
            }
        }
        // controller output
        else if(strcmp(argv[i], "--controller-output") == 0)
        {
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
                    if(find(global_config.controller.controller_output.begin(), global_config.controller.controller_output.end(), argv[i]) == global_config.controller.controller_output.end())
                    {
                        global_config.controller.controller_output.push_back(argv[i]);
                    }
                    i++;
                }
            }
        }
        // controller output
        else if(strcmp(argv[i], "--controller-input") == 0)
        {
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
                    if(find(global_config.controller.controller_input.begin(), global_config.controller.controller_input.end(), argv[i]) == global_config.controller.controller_input.end())
                    {
                        global_config.controller.controller_input.push_back(argv[i]);
                    }
                    i++;
                }
            }
        }
        // noise variance map
//        else if(strcmp(argv[i], "--noise-variance") == 0)
//        {
//            //global_config.partition_nondet = true;
//            i++;
//            bool map_end = false;
//            while (!map_end)
//            {
//                if (is_flag(argv[i]) || is_drh(argv[i]) || is_pdrh(argv[i]))
//                {
//                    map_end = true;
//                    i--;
//                }
//                else
//                {
//                    istringstream var_is(argv[i]);
//                    string var = var_is.str();
//                    i++;
//                    if (is_flag(argv[i]) || is_drh(argv[i]) || is_pdrh(argv[i]))
//                    {
//                        CLOG(ERROR, "config") << "partition precision for variable \"" << var << "\" is not defined";
//                        exit(EXIT_FAILURE);
//                    }
//                    else
//                    {
//                        istringstream val_is(argv[i]);
//                        global_config.controller.noise_variance.insert(
//                                make_pair(var, capd::interval(val_is.str(), val_is.str()).rightBound()));
//                        i++;
//                    }
//                }
//            }
//        }
        // global_time variable
        else if(strcmp(argv[i], "--global-time") == 0)
        {
            i++;
            global_config.global_time = argv[i];
        }
        // sample_time variable
        else if(strcmp(argv[i], "--sample-time") == 0)
        {
            i++;
            global_config.sample_time = argv[i];
        }
        // noise variance
        else if(strcmp(argv[i], "--noise-variance") == 0)
        {
            i++;
            istringstream is(argv[i]);
            is >> global_config.noise_var;
            if (global_config.noise_var <= 0)
            {
                CLOG(ERROR, "config") << "noise variance should be positive";
                exit(EXIT_FAILURE);
            }
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
        // qmc conf
        else if(strcmp(argv[i], "--qmc-conf") == 0)
        {
            global_config.qmc_flag = true;
            global_config.stat_flag = true;
            i++;
            istringstream is(argv[i]);
            is >> global_config.qmc_conf;
            if (global_config.qmc_conf <= 0)
            {
                CLOG(ERROR, "config") << "confidence for QMC method should be positive";
                exit(EXIT_FAILURE);
            }
        }
            // qmc acc
        else if(strcmp(argv[i], "--qmc-acc") == 0)
        {
            global_config.qmc_flag = true;
            global_config.stat_flag = true;
            i++;
            istringstream is(argv[i]);
            is >> global_config.qmc_acc;
            if (global_config.qmc_acc < 0)
            {
                CLOG(ERROR, "config") << "accuracy for QMS simulations should be positive";
                exit(EXIT_FAILURE);
            }
        }
        // qmc sample size
        else if(strcmp(argv[i], "--qmc-sample-size") == 0)
        {
            global_config.qmc_flag = true;
            global_config.stat_flag = true;
            i++;
            istringstream is(argv[i]);
            is >> global_config.qmc_sample_size;
            if (global_config.qmc_sample_size <= 0)
            {
                CLOG(ERROR, "config") << "number of samples for QMC method should be positive";
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
        // show model flag
        else if(strcmp(argv[i], "--show-model") == 0)
        {
            global_config.show_model = true;
        }
        // ignore nondeterministic parameters termination condition
        else if(strcmp(argv[i], "--ignore-nondet") == 0)
        {
            global_config.ignore_nondet = true;
        }
        // debug flag
        else if(strcmp(argv[i], "--debug") == 0)
        {
            global_config.debug = true;
        }
        // debug flag
        else if(strcmp(argv[i], "--sort-rv") == 0)
        {
            global_config.sort_rv_flag = true;
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
    // checking secondary solver type
    if(global_config.secondary_solver_type == solver::type::UNKNOWN_SOLVER)
    {
        global_config.secondary_solver_type = global_config.solver_type;
        global_config.secondary_solver_bin = global_config.solver_bin;
    }
}

void print_usage()
{
    cout << endl;
    cout << "Usage:" << endl;
    cout << endl;
    cout << "	ProbReach <options> <file.pdrh/file.drh> <solver-options>" << endl;
    cout << endl;
    cout << "general options:" << endl;
    cout << "-h/--help - displays help message" << endl;
    cout << "-k <int> - defines the reachability depth (default: the shortest path length if exists)" << endl;
    cout << "-l <int> - defines the reachability depth lower bound (cannot be used without -u; default: the shortest path length if exists)" << endl;
    cout << "-u <int> - defines the reachability depth upper bound (cannot be used without -l; default: the shortest path length if exists)" << endl;
    cout << "-t <int> - number of CPU cores (default: " << global_config.max_num_threads << ") (max " << global_config.max_num_threads << ")" << endl;
    cout << "--verbose - outputs computation details (default: " << global_config.verbose << ")" << endl;
    cout << "--verbose-result - outputs the runtime and the number of samples (statistical model checking only; default: " << global_config.verbose_result << ")" << endl;
    cout << "--version - displays current version of the tool" << endl;
    cout << endl;
    cout << "solver related options:" << endl;
    cout << "--delta-sat - uses the delta-sat answer of dReal to conclude about satisfiability of the evaluated formula (statistical model checking and hybrid automata only; default: " << global_config.delta_sat << ")" << endl;
    cout << "--solver <path> - full path to the solver (default: " << global_config.solver_bin << ")" << endl;
    cout << endl;
    cout << "special options:" << endl;
    cout << "--time-var-name <string> - the name of the variable representing time in the model (default: " << global_config.time_var_name << ")" << endl;
    cout << endl;
    cout << "statistical model checking options:" << endl;
    cout << "--bayesian-acc <double> - half-length of the confidence interval in Bayesian estimations (default: " << global_config.bayesian_acc << ")" << endl;
    cout << "--bayesian-conf <double> - confidence value in Bayesian estimations (default: " << global_config.bayesian_conf << ")" << endl;
    cout << "--cross-entropy - enables Cross-Entropy algorithm (default: " << global_config.cross_entropy_flag << ")" << endl;
    cout << "--cross-entropy-term-arg <double> - termination argument (variance) for Cross-Entropy algorithm (default: " << global_config.cross_entropy_term_arg << ")" << endl;
    cout << "--chernoff-acc <double> - half-length of the confidence interval in Chernoff-Hoeffding method (default: " << global_config.chernoff_acc << ")" << endl;
    cout << "--chernoff-conf <double> - confidence value in Chernoff-Hoeffding method (default: " << global_config.chernoff_conf << ")" << endl;
    cout << "--elite-ratio <double> - defines the fraction of the sample size - elite samples which are used in Cross-Entropy algorithm for updating the distribution parameters (default: " << global_config.elite_ratio << ")" << endl;
    cout << "--min-prob - computes confidence interval for the minimum reachability probability (default: " << global_config.min_prob << ")" << endl;
    cout << "--sample-size <int> - number of sample per iteration of Cross-Entropy algorithm (default: " << global_config.sample_size << ")" << endl;
    cout << endl;
    cout << "formal method options:" << endl;
    cout << "-e/--precision-prob <double> - length of the probability enclosure (default: " << global_config.precision_prob << ")" << endl;
    cout << "--integral-inf-coeff <double> - ratio for the continuous random variables with unbounded support (default: " << global_config.integral_inf_coeff << ")" << endl;
    cout << "--integral-pdf-step <double> - step value used for bounding domains of unbounded continuous random variables (default " << global_config.integral_pdf_step << ")" << endl;
    cout << "--partition-nondet - partitions the domain nondeterministic parameters up to the value defined in --precision-nondet (default: " << global_config.partition_nondet << ")" << endl;
    cout << "--partition-prob - obtains a partition of the domain of continuous random parameters satisfying -e/--precision-prob (default: " << global_config.partition_prob << ")" << endl;
    cout << "--precision-nondet [<var> <double>] - defines the precision vector for the nondeterministic parameters" << endl;
    cout << "--precision-ratio <double> - used to define precision passed to the solver as (solver-precision = min-box-dimension * precision-ratio) (default: " << global_config.solver_precision_ratio << ")" << endl;
    cout << endl;
}

void print_version()
{
    cout << "ProbReach " << PROBREACH_VERSION << " (" << git::get_sha1() << ")" << endl;
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