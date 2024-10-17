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
#include "naive.h"
#include "git_sha1.h"
#include "version.h"
#include "box.h"
#include "pdrh2box.h"
#include "mc.h"
#include "pdrh_config.h"
#include "stability.h"

#ifdef _OPENMP
#include <omp.h>
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
using namespace naive;

//// the minimum depth of each path
//size_t min_depth = 0;
//// the maximum depth of each path
//size_t max_depth = 0;
//// number of point used in IVP solving
//size_t num_points = 1;
//// path to the input file
//string in_file = "";
//// minimisation flag
//bool minimise_flag = false;
//// half-size of the computed confidence intervals
//double acc = 1e-1;
//// confidence value for the computed confidence intervals
//double conf = 0.95;
//// number of iterations of cross-entropy algorithm
//size_t num_iter = 2;
//// number of sample of each iteration of cross-entropy algorithm
//size_t num_samples = 10;
//// number of threads
//#ifdef _OPENMP
//    int num_threads = omp_get_max_threads();
//#else
//    int num_threads = 1;
//#endif
//

//// printing help message
//void print_help()
//{
//    cout << "Usage:" << endl;
//    cout << endl;
//    cout << "	simulate <options> <file.pdrh/file.drh> <solver-options>" << endl;
//    cout << endl;
//    cout << "options:" << endl;
//    cout << "-h - displays help message" << endl;
//    cout << "-v - prints out the current version of ProbReach" << endl;
//    cout << "-l - minimum depth of every simulation path (default = " << min_depth << ")" << endl;
//    cout << "-u - maximum depth of every simulation path (default = " << max_depth << ")" << endl;
//    cout << "-n - number of points used in non-rigorous IVP solving (default = " << num_points << ")" << endl;
//    #ifdef _OPENMP
//        cout << "-t - number of threads (default = " << num_threads << ", max = " << omp_get_max_threads() << ")" << endl;
//    #endif
//    cout << "--min - minimise reachability probability (default = " << minimise_flag << ")" << endl;
//    cout << "--acc - half-size of the computed confidence intervals (default = " << acc << ")" << endl;
//    cout << "--conf - confidence value for the computed confidence intervals (default = " << conf << ")" << endl;
//    cout << "--iter - confidence value for the computed confidence intervals (default = " << num_iter << ")" << endl;
//    cout << "--samples - number of samples for each iteration of cross-entropy algorithm (default = " << num_samples << ")" << endl;
//    cout << "--solver - full path to the solver executable (default = " << dreal::solver_bin << ")" << endl;
////    cout << "--params - list of controller parameters (default = " << dreal::solver_bin << ")" << endl;
//}

//// parsing command line options
//void parse_cmd(int argc, char* argv[])
//{
//    //parsing ProbReach options
//    for(int i = 1; i < argc; i++)
//    {
//        // filename
//        if(string(argv[i]).substr(string(argv[i]).find_last_of('.') + 1) == "pdrh" ||
//                string(argv[i]).substr(string(argv[i]).find_last_of('.') + 1) == "drh")
//        {
//            in_file = argv[i];
//        }
//        // minimisation flag
//        if(string(argv[i]) == "--minimise")
//        {
//            minimise_flag = true;
//        }
//        // help
//        else if(string(argv[i]) == "-h")
//        {
//            print_help();
//            exit(EXIT_SUCCESS);
//        }
//        // version
//        else if(string(argv[i]) == "-v")
//        {
//            cout << "ProbReach " << PROBREACH_VERSION << " (" << git::get_sha1() << ")" << endl;
//            exit(EXIT_SUCCESS);
//        }
//        // minimum path length
//        else if (string(argv[i]) == "-l")
//        {
//            i++;
//            istringstream is(argv[i]);
//            is >> min_depth;
//            if (min_depth < 0)
//            {
//                cerr << "-l must be positive and not larger than -u";
//                exit(EXIT_FAILURE);
//            }
//        }
//        // maximum path length
//        else if (string(argv[i]) == "-u")
//        {
//            i++;
//            istringstream is(argv[i]);
//            is >> max_depth;
//            if (max_depth < 0)
//            {
//                cerr << "-u must be positive and not smaller than -l";
//                exit(EXIT_FAILURE);
//            }
//        }
//        // maximum number of points
//        else if (string(argv[i]) == "-n")
//        {
//            i++;
//            istringstream is(argv[i]);
//            is >> num_points;
//            if (num_points < 0)
//            {
//                cerr << "-n must be positive";
//                exit(EXIT_FAILURE);
//            }
//        }
//        // number of threads
//        else if(strcmp(argv[i], "-t") == 0)
//        {
//            i++;
//            istringstream is(argv[i]);
//            is >> num_threads;
//            if(num_threads <= omp_get_max_threads())
//            {
//                if(num_threads > 0)
//                {
//                    #ifdef _OPENMP
//                        omp_set_num_threads(num_threads);
//                    #endif
//                }
//                else
//                {
//                    cerr << "Number of cores should be positive";
//                    exit(EXIT_FAILURE);
//                }
//            }
//            else
//            {
//                cerr << "Max number of cores available is " << omp_get_max_threads() << ". You specified " << num_threads;
//                exit(EXIT_FAILURE);
//            }
//        }
//        // accuracy
//        else if ((strcmp(argv[i], "--acc") == 0))
//        {
//            i++;
//            istringstream is(argv[i]);
//            is >> acc;
//            if (acc < 0)
//            {
//                cerr << "--acc must be positive";
//                exit(EXIT_FAILURE);
//            }
//        }
//        // confidence
//        else if ((strcmp(argv[i], "--conf") == 0))
//        {
//            i++;
//            istringstream is(argv[i]);
//            is >> conf;
//            if (conf <= 0 || conf >= 1)
//            {
//                cerr << "--conf must be a number from (0,1) interval";
//                exit(EXIT_FAILURE);
//            }
//        }
//        // number of iterations
//        else if ((strcmp(argv[i], "--iter") == 0))
//        {
//            i++;
//            istringstream is(argv[i]);
//            is >> num_iter;
//            if (num_iter <= 0)
//            {
//                cerr << "--iter must be positive";
//                exit(EXIT_FAILURE);
//            }
//        }
//        // number of samples per iteration of cross-entropy algorithm
//        else if ((strcmp(argv[i], "--samples") == 0))
//        {
//            i++;
//            istringstream is(argv[i]);
//            is >> num_samples;
//            if (num_samples <= 0)
//            {
//                cerr << "--samples must be positive";
//                exit(EXIT_FAILURE);
//            }
//        }
//        else if(string(argv[i]) == "--solver")
//        {
//            i++;
//            dreal::solver_bin = string(argv[i]);
//        }
//    }
//    // checking if the input file is specified
//    if(in_file == "")
//    {
//        cerr << "Input file has not been specified" << endl;
//        exit(EXIT_FAILURE);
//    }
//}

int main(int argc, char *argv[])
{
  //    cout << dreal::solver_bin << endl;
  //    cout << dreal::cmd_args << endl;
  // parsing command line arguments
  // parse_cmd(argc, argv);
  // parsing pdrh config here
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

  cout << "Precision prob: " << global_config.precision_prob << endl;

  START_EASYLOGGINGPP(argc, argv);
  el::Logger *algorithm_logger = el::Loggers::getLogger("algorithm");

  //    global_config.verbose_result = true;
  ////    global_config.bayesian_flag = true;
  //    global_config.reach_depth_max = max_depth;
  //    global_config.reach_depth_min = min_depth;

  //    cout << "Accuracy: " << acc << endl;

  //    cout << pdrh::model_to_string() << endl;

  // the main algorithm is here
  box nondet_domain = pdrh2box::get_nondet_domain();
  cout << "Domain of nondeterministic parameters: " << nondet_domain << endl;
  // copying the parameter map
  map<string, pair<pdrh::node *, pdrh::node *>> init_par_map;
  for (auto it = pdrh::par_map.begin(); it != pdrh::par_map.end(); it++)
  {
    init_par_map[it->first] = make_pair(
      pdrh::copy_node(it->second.first), pdrh::copy_node(it->second.second));
  }
  // nondeterministic parameters names
  vector<string> param_names = {"Kp", "Ki", "Kd"};
  cout << "Param map:" << endl;
  for (auto it = pdrh::par_map.begin(); it != pdrh::par_map.end(); it++)
  {
    cout << it->first << "[" << pdrh::node_to_string_infix(it->second.first)
         << ", " << pdrh::node_to_string_infix(it->second.second) << "]"
         << endl;
  }
  // changing the domain to start with the simplest controller
  pdrh::node *zero_node = new pdrh::node("0");
  for (string param : param_names)
  {
    pdrh::par_map[param] = make_pair(zero_node, zero_node);
    cout << param << " : "
         << pdrh::node_to_string_infix(pdrh::par_map[param].first) << endl;
  }
  pair<box, capd::interval> res = make_pair(box(), capd::interval(0.0));
  if (global_config.min_prob)
    res.second = capd::interval(1.0);
  // iterating through all parameter values
  for (string param : param_names)
  {
    // increasing complexity of the controller
    pdrh::par_map[param] = init_par_map[param];
    cout << "Domain of nondeterministic parameters: "
         << pdrh2box::get_nondet_domain() << endl;
    capd::interval conf_intersection(0);
    // adjusting discretisation until both intervals intersect by more than 80%
    // use the size of optimised conf interval instead of the accuracy value of the statistical algorithm
    while (capd::intervals::width(conf_intersection) <
           global_config.precision_prob)
    {
      // cross entropy algorithm is used here
      global_config.decision_method = 2;
      cout << "Solving optimisation problem for the discretised system" << endl;
      cout << "Discretisation using " << global_config.ode_discretisation
           << " points" << endl;
      pair<box, capd::interval> opt_res =
        algorithm::evaluate_npha_cross_entropy_normal(
          global_config.reach_depth_min,
          global_config.reach_depth_max,
          global_config.sample_size,
          global_config.iter_num,
          global_config.precision_prob,
          global_config.conf,
          stability::is_stable);
      cout << "Optimisation result: " << endl;
      cout << opt_res.first << "   |   " << opt_res.second << endl;
      global_config.decision_method = 1;
      cout << "Computing confidence interval with guarantees:" << endl;
      capd::interval prob = algorithm::evaluate_pha_bayesian(
        global_config.reach_depth_min,
        global_config.reach_depth_max,
        global_config.precision_prob,
        global_config.conf,
        {opt_res.first});
      cout << "The verification result:" << endl;
      cout << opt_res.first << "   |   " << prob << endl;
      capd::intervals::intersection(opt_res.second, prob, conf_intersection);
      cout << "Intersection of the two confidence intervals: "
           << conf_intersection << endl;
      // increasing the number of points used for odes discretisation
      if (
        capd::intervals::width(conf_intersection) <
        global_config.precision_prob)
      {
        global_config.ode_discretisation *= 2;
      }
      // updating the result
      // the case of minimising the probability value
      if (global_config.min_prob)
      {
        // comparing probability intervals by their mid points
        if (prob.mid() <= res.second.mid())
          res = make_pair(opt_res.first, prob);
      }
      // maximising the probability
      else
      {
        // comparing probability intervals by their mid points
        if (prob.mid() >= res.second.mid())
          res = make_pair(opt_res.first, prob);
      }
      cout << "Best result so far:" << endl;
      cout << res.first << "   |   " << res.second << endl;
      if (
        capd::intervals::width(conf_intersection) <
          global_config.precision_prob &&
        (conf_intersection.rightBound() >= 1 ||
         conf_intersection.leftBound() <= 0))
      {
        break;
      }
    }
    cout << "Updating controller's complexity" << endl << endl;
    // doubling the number of samples per iteration
    global_config.sample_size *= 2;
    // incrementing the number of iterations
    global_config.iter_num++;
  }
  // removing zero node
  delete zero_node;
  cout << "Final verdict:" << endl;
  cout << res.first << "   |   " << res.second << endl;

  el::Loggers::unregisterLogger("algorithm");

  return 0;
}
