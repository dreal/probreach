//
// Created by fedor on 04/03/16.
//

#include <iostream>
#include <sstream>
#include "parser/csv/csvparser.h"
#include <iomanip>
#include <pdrh.h>
#include <model.h>
#include <solver/dreal_wrapper.h>
#include <util/pdrh2box.h>
#include "pdrh_config.h"
#include "pdrh.h"
#include "algorithm.h"
#include "rnd.h"
#include "parser/output/outputparser.h"
#include "ap.h"
#include "box.h"
#include "qmc.h"

extern "C"
{
    #include "pdrhparser.h"
}

#include "easylogging++.h"

extern "C" int yyparse();
extern "C" FILE *yyin;

INITIALIZE_EASYLOGGINGPP

void parse_pdrh(string filename)
{
    CLOG_IF(global_config.verbose, INFO, "parser") << "Model file: " << filename;
    FILE *pdrhfile = fopen(filename.c_str(), "r");
    if (!pdrhfile)
    {
        CLOG(ERROR, "parser") << "Couldn't open " << filename;
        exit(EXIT_FAILURE);
    }
    std::stringstream s, pdrhnameprep;
    pdrhnameprep << filename << ".preprocessed";
    s << "cpp -w -P " << filename << " > " << pdrhnameprep.str().c_str();
    int res = system(s.str().c_str());
    // cheking the result of system call
    if(res != 0)
    {
        CLOG(ERROR, "parser") << "Problem occured while preprocessing " << filename;
        exit(EXIT_FAILURE);
    }
    // parsing the preprocessed file
    FILE *pdrhfileprep = fopen(pdrhnameprep.str().c_str(), "r");
    // make sure it's valid:
    if (!pdrhfileprep)
    {
        CLOG(ERROR, "parser") << "Couldn't open " << pdrhnameprep.str();
        exit(EXIT_FAILURE);
    }
    // set lex to read from it instead of defaulting to STDIN:
    yyin = pdrhfileprep;
    // parse through the input until there is no more:
    do
    {
        yyparse();
    }
    while (!feof(yyin));
    remove(pdrhnameprep.str().c_str());
    CLOG_IF(global_config.verbose, INFO, "parser") << "OK";
}

int main(int argc, char* argv[])
{
    START_EASYLOGGINGPP(argc, argv);
    el::Logger* parser_logger = el::Loggers::getLogger("parser");
    el::Logger* algorithm_logger = el::Loggers::getLogger("algorithm");
    el::Logger* solver_logger = el::Loggers::getLogger("solver");
    el::Logger* series_parser_logger = el::Loggers::getLogger("series-parser");
    el::Logger* config_parser_logger = el::Loggers::getLogger("config");
    el::Logger* rng_logger = el::Loggers::getLogger("ran_gen");
    el::Logger* model_logger = el::Loggers::getLogger("model");

    // parse command line
    parse_pdrh_config(argc, argv);

    // setting precision on the output
    cout.precision(16);
    //cout << scientific;
    // pdrh parser
    parse_pdrh(global_config.model_filename);

    // setting the model type automatically here
    pdrh::set_model_type();

    // printing the model if the flag is set
    if(global_config.show_model)
    {
        cout << pdrh::model_to_string() << endl;
    }

    // displaying primary solver
//    CLOG_IF(global_config.verbose_result, INFO, "parser") << "Model type: " << pdrh::model_type;
//    if(global_config.solver_type == solver::type::DREAL)
//    {
//        CLOG_IF(global_config.verbose_result, INFO, "parser") << "Primary solver: dReal";
//    }
//    else if(global_config.solver_type == solver::type::ISAT)
//    {
//        CLOG_IF(global_config.verbose_result, INFO, "parser") << "Primary solver: iSAT";
//    }
//    else if(global_config.solver_type == solver::type::UNKNOWN_SOLVER)
//    {
//        CLOG(ERROR, "parser") << "Primary solver is not defined";
//        return EXIT_FAILURE;
//    }
//    // displaying secondary solver
//    if(global_config.secondary_solver_bin.empty())
//    {
//        CLOG_IF(global_config.verbose_result, INFO, "parser") << "Secondary solver: not defined";
//    }
//    else
//    {
//        if(global_config.secondary_solver_type == solver::type::DREAL)
//        {
//            CLOG_IF(global_config.verbose_result, INFO, "parser") << "Secondary solver: dReal";
//        }
//        else if(global_config.secondary_solver_type == solver::type::ISAT)
//        {
//            CLOG_IF(global_config.verbose_result, INFO, "parser") << "Secondary solver: iSAT";
//        }
//        else if(global_config.secondary_solver_type == solver::type::UNKNOWN_SOLVER)
//        {
//            CLOG(ERROR, "parser") << "Secondary solver is not recognized";
//            return EXIT_FAILURE;
//        }
//    }

    vector<vector<pdrh::mode*>> paths = pdrh::get_paths();
    cout << "Set of paths to check: " << endl;
    if(paths.size() > 0)
    {
        for(vector<pdrh::mode*> path : paths)
        {
            for(pdrh::mode* m : path)
            {
                cout << m->id << ", ";
            }
            cout << endl;
        }
    }
    else
    {
        cout << "To determine from the command line options" << endl;
    }

    switch(pdrh::model_type)
    {
        // hybrid automata
        case pdrh::HA:
        {
//            int res = algorithm::evaluate_ha(global_config.reach_depth_min, global_config.reach_depth_max);
//            if (res == decision_procedure::SAT)
//            {
//                std::cout << "sat" << std::endl;
//            }
//            else if (res == decision_procedure::UNDET)
//            {
//                std::cout << "undet" << std::endl;
//            }
//            else if (res == decision_procedure::UNSAT)
//            {
//                std::cout << "unsat" << std::endl;
//            }
//            else if (res == decision_procedure::ERROR)
//            {
//                std::cout << "error" << std::endl;
//                return EXIT_FAILURE;
//            }
//            break;
            //cout << "Simulating a path: " << ap::simulate_path(ap::get_all_paths({}).front(), ap::init_to_box({}), {}) << endl;
            //cout << global_config.global_time << endl;
            //cout << global_config.sample_time << endl;
            //global_config.ode_discretisation = 1;
            //cout << "Noise variance: " << global_config.noise_var << endl;
            //cout << "Simulation: " << ap::simulate({}) << endl;
            cout << "Verification: " << ap::verify({}) << endl;
            break;
        }
        // probabilistic hybrid automata
        case pdrh::PHA:
        {
            capd::interval probability;
            if(global_config.chernoff_flag)
            {
                probability = algorithm::evaluate_pha_chernoff(global_config.reach_depth_min, global_config.reach_depth_max, global_config.chernoff_acc, global_config.chernoff_conf);
            }
            else if(global_config.bayesian_flag)
            {
                probability = algorithm::evaluate_pha_bayesian(global_config.reach_depth_min, global_config.reach_depth_max, global_config.bayesian_acc, global_config.bayesian_conf);
            }
            else
            {
                probability = algorithm::evaluate_pha(global_config.reach_depth_min, global_config.reach_depth_max);
            }
            // modifying the interval if outside (0,1)
            if(probability.leftBound() < 0)
            {
                probability.setLeftBound(0);
            }
            if(probability.rightBound() > 1)
            {
                probability.setRightBound(1);
            }
            std::cout << scientific << probability << " | " << capd::intervals::width(probability) << std::endl;
//            cout << "UNSAT samples:" << endl;
//            for(box b : ap::unsat_samples)
//            {
//                cout << b << endl;
//            }
//            break;
        }
        // nondeterministic probabilistic hybrid automata
        case pdrh::NPHA:
        {
            if(global_config.sobol_flag)
            {
                pair<box, capd::interval> probability = algorithm::evaluate_npha_sobol(global_config.reach_depth_min,
                                                                                       global_config.reach_depth_max,
                                                                                       global_config.sample_size);
                std::cout << probability.first << " : " << probability.second << " | " << capd::intervals::width(probability.second) << std::endl;
            }
            else if(global_config.cross_entropy_flag)
            {
                // just a temporary fix. come back to it !!!
                if(pdrh::par_map.empty())
                {
                    capd::interval probability;
                    if(global_config.chernoff_flag)
                    {
                        probability = algorithm::evaluate_pha_chernoff(global_config.reach_depth_min, global_config.reach_depth_max, global_config.chernoff_acc, global_config.chernoff_conf);
                    }
                    else if(global_config.bayesian_flag)
                    {
                        probability = algorithm::evaluate_pha_bayesian(global_config.reach_depth_min, global_config.reach_depth_max, global_config.bayesian_acc, global_config.bayesian_conf);
                    }
                    else if(global_config.qmc_flag)
                    {
                        if (global_config.CI_flag==1) {
                            probability = algorithm::evaluate_pha_qmc(1);
                        } else if (global_config.CI_flag==2){
                            probability = algorithm::evaluate_pha_qmc(2);
                        } else if (global_config.CI_flag==3){
                            probability = algorithm::evaluate_pha_qmc(3);
                        } else if (global_config.CI_flag==4){
                            probability = algorithm::evaluate_pha_qmc(4);
                        } else if (global_config.CI_flag==5){
                            probability = algorithm::evaluate_pha_qmc(5);
                        } else if (global_config.CI_flag==6){
                            probability = algorithm::evaluate_pha_qmc(6);
                        } else if (global_config.CI_flag==7){
                            probability = algorithm::evaluate_pha_qmc(7);
                        } else if (global_config.CI_flag==8){
                            probability = algorithm::evaluate_pha_qmc(8);
                        } else
                            probability = algorithm::evaluate_pha_qmc(0);

                    } else
                    {
                        cout << "Statistical method is not chosen" << endl;
                        return EXIT_FAILURE;
                    }
                    cout << scientific << probability << " | " << capd::intervals::width(probability) << endl;
                }
                else
                {
                    // getting the domain of nondeterministic parameters
                    box nondet_domain = pdrh2box::get_nondet_domain();
                    cout << "Domain of nondeterministic parameters: " << nondet_domain << endl;
                    // copying the parameter map
                    map<string, pair<pdrh::node*, pdrh::node*>> init_par_map;
                    for(auto it = pdrh::par_map.begin(); it != pdrh::par_map.end(); it++)
                    {
                        init_par_map[it->first] = make_pair(pdrh::copy_node(it->second.first), pdrh::copy_node(it->second.second));
                    }
                    // nondeterministic parameters names
                    vector<string> param_names = {"Kp", "Ki", "Kd"};
                    // changing the domain to start with the simplest controller
                    pdrh::node *zero_node = new pdrh::node("0");
                    for(string param : param_names)
                    {
                        pdrh::par_map[param] = make_pair(zero_node, zero_node);
                    }
                    pair<box, capd::interval> res = make_pair(box(), capd::interval(0.0));
                    if(global_config.min_prob) res.second = capd::interval(1.0);
                    // iterating through all parameter values
                    for(string param : param_names)
                    {
                        // increasing complexity of the controller
                        pdrh::par_map[param] = init_par_map[param];
                        cout << "Domain of nondeterministic parameters: " << pdrh2box::get_nondet_domain() << endl;
                        capd::interval conf_intersection(0);
                        // adjusting discretisation until both intervals intersect by more than 80%
                        // use the size of optimised conf interval instead of the accuracy value of the statistical algorithm
                        while(capd::intervals::width(conf_intersection) < global_config.bayesian_acc)
                        {
                            // cross entropy algorithm is used here
                            global_config.use_verified = false;
                            cout << "Solving optimisation problem for the discretised system" << endl;
                            cout << "Discretisation using " << global_config.ode_discretisation << " points" << endl;
//                            pair<box, capd::interval> opt_res = make_pair(box("Kp:[1.77,1.77];Ki:[0,0];Kd:[0,0];"), capd::interval(0));
                            pair<box, capd::interval> opt_res = algorithm::evaluate_npha_cross_entropy_normal( global_config.reach_depth_min,
                                                                                                               global_config.reach_depth_max,
                                                                                                               global_config.sample_size);
                            cout << "Optimisation result: " << endl;
                            cout << opt_res.first << "   |   " << opt_res.second << endl;
                            global_config.use_verified = true;
                            cout << "Computing confidence interval with guarantees:" << endl;
                            capd::interval prob = algorithm::evaluate_pha_bayesian(global_config.reach_depth_min, global_config.reach_depth_max, global_config.bayesian_acc,
                                                                                   global_config.bayesian_conf, {opt_res.first});
//                            capd::interval prob = opt_res.second;
                            cout << "The verification result:" << endl;
                            cout << opt_res.first << "   |   " << prob << endl;
                            capd::intervals::intersection(opt_res.second, prob, conf_intersection);
                            cout << "Intersection of the two confidence intervals: " << conf_intersection << endl;
                            // increasing the number of points used for odes discretisation
                            if(capd::intervals::width(conf_intersection) < global_config.bayesian_acc)
                            {
                                global_config.ode_discretisation *= 2;
                            }
                            // updating the result
                            // the case of minimising the probability value
                            if(global_config.min_prob)
                            {
                                // comparing probability intervals by their mid points
                                if(prob.mid() <= res.second.mid()) res = make_pair(opt_res.first, prob);
                            }
                            // maximising the probability
                            else
                            {
                                // comparing probability intervals by their mid points
                                if(prob.mid() >= res.second.mid()) res = make_pair(opt_res.first, prob);
                            }
                            cout << "Best result so far:" << endl;
                            cout << res.first << "   |   " << res.second << endl;
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

//                    if(global_config.cross_entropy_beta)
//                    {
//                        opt_res = algorithm::evaluate_npha_cross_entropy_beta( global_config.reach_depth_min,
//                                                                                   global_config.reach_depth_max,
//                                                                                   global_config.sample_size);
//                    }
                    //std::cout << scientific << probability.first << " : " << probability.second << " | " << capd::intervals::width(probability.second) << std::endl;
                }
//                cout << "UNSAT samples:" << endl;
//                for(box b : ap::unsat_samples)
//                {
//                    cout << b << endl;
//                }
            }
            else
            {
                std::map<box, capd::interval> probability_map = algorithm::evaluate_npha(global_config.reach_depth_min, global_config.reach_depth_max);
                for(auto it = probability_map.cbegin(); it != probability_map.cend(); it++)
                {
                    std::cout << scientific << it->first << " | " << it->second << std::endl;
                }
            }
            break;


//            pair<capd::interval, box> res = algorithm::solve_min_max();
//            cout << res.second << " | " << res.first << endl;
//            break;
        }
        // parameter synthesis
        case pdrh::PSY:
        {
            //CLOG(ERROR, "algorithm") << "Parameter synthesis is currently not supported";
            //exit(EXIT_FAILURE);
            if(global_config.series_filename.empty())
            {
                CLOG(ERROR, "series-parser") << "Time series file is not specified";
                return EXIT_FAILURE;
            }
            map<string, vector<pair<pdrh::node*, pdrh::node*>>> time_series = csvparser::parse(global_config.series_filename);
            tuple<vector<box>, vector<box>, vector<box>> boxes = algorithm::evaluate_psy(time_series);
            vector<box> sat_boxes = get<0>(boxes);
            vector<box> undet_boxes = get<1>(boxes);
            vector<box> unsat_boxes = get<2>(boxes);
            cout << "sat" << endl;
            for(box b : sat_boxes)
            {
                cout << b << endl;
            }
            cout << "undet" << endl;
            for(box b : undet_boxes)
            {
                cout << b << endl;
            }
            cout << "unsat" << endl;
            for(box b : unsat_boxes)
            {
                cout << b << endl;
            }
            break;
        }
        case pdrh::NHA:
        {
            CLOG(ERROR, "algorithm") << "Nondeterministic hybrid automata is currently not supported";
            exit(EXIT_FAILURE);
            //break;
        }
    }

//    capd::interval alpha("0.7854","0.7854");
//    capd::interval v0("25","25");
//    capd::interval g("9.8","9.8");
//    capd::interval Sx("100","100");
//
//    capd::interval ref_interval = sqrt((Sx*g) / (2*v0*v0*cos(alpha)*sin(alpha))-1);
//    map<string, capd::interval> ref_map;
//    ref_map.insert(make_pair("K", ref_interval));
//    box ref_box(ref_map);
//    cout << "Ref box:" << endl;
//    cout << setprecision(16) << ref_box << endl;
//
//    capd::interval lower_bound = sqrt( (Sx * g) / (sin(2 * alpha) * (0.7*0.7 + 1)) );
//    cout << setprecision(16) << lower_bound << endl;

    // unregister the loggers
    el::Loggers::unregisterLogger("parser");
    el::Loggers::unregisterLogger("algorithm");
    el::Loggers::unregisterLogger("solver");
    el::Loggers::unregisterLogger("series-parser");
    el::Loggers::unregisterLogger("config");
    el::Loggers::unregisterLogger("ran_gen");
    el::Loggers::unregisterLogger("model");
    return EXIT_SUCCESS;
}