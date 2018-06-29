//
// Created by fedor on 24/02/16.
//

#ifndef PROBREACH_PDRH_CONTEXT_H
#define PROBREACH_PDRH_CONTEXT_H

#include <string>
#include <map>
#include <vector>

struct pdrh_config
{
    bool stat_flag = false;
    // verified integration options
    double integral_inf_coeff = 1e-01;
    double integral_pdf_step = 1e-01;
    // solver options
    //string solver_bin = SOLVER_BIN;
    std::string solver_bin = "dReal";
    std::string solver_opt = "";
//    solver::type solver_type = solver::type::UNKNOWN_SOLVER;
    std::string secondary_solver_bin = "";
//    solver::type secondary_solver_type = solver::type::UNKNOWN_SOLVER;
    // algorithm options
    double precision_prob = 1e-03;
    double precision_prob_single = 1e-03;
    double precision_nondet = 1e-03;
    bool partition_prob = false;
    bool partition_nondet = false;
    std::map<std::string, std::string> partition_prob_map;
    std::map<std::string, std::string> partition_nondet_map;
    bool partition_psy = false;
    double solver_precision_ratio = 1e-03;
    unsigned int solver_timeout = 10; // seconds
    int reach_depth_min = 0;
    int reach_depth_max = 0;
    bool verbose_result = false;
    bool witness_guided = false;
    // boxes options
    bool boxes_prepartition = false;
    bool boxes_merge = false;
    // model options
    std::string model_filename;
    std::string series_filename;
    // output options
    bool verbose = false;
    bool xml_output = false;
    // parallelization options
    int max_num_threads = 1;
    int num_threads = max_num_threads;
    // sampling options
    double chernoff_acc = 1e-2;
    double chernoff_conf = 0.99;
    bool chernoff_flag = false;
    double bayesian_acc = 1e-2;
    double bayesian_conf = 0.99;
    bool bayesian_flag = false;
    // qmc flags
    bool qmc_flag = false;
    double qmc_conf = 0.99;
    double qmc_acc = 1e-2;
    long qmc_sample_size = 10000;

    bool delta_sat = false;
    std::vector<std::string> time_var_name = {"tau"};
    double elite_ratio = 0.1;
    double sobol_term_arg = 1e-2;
    bool max_prob = true;
    bool min_prob = false;
    bool sobol_flag = false;
    bool cross_entropy_flag = false;
    bool cross_entropy_normal = true;
    bool cross_entropy_beta = false;
    double cross_entropy_term_arg = 1e-2;
    bool ignore_nondet = false;
    bool debug = false;
    bool sort_rv_flag = false;
    bool show_model = false;
    int sample_size = 20;
    int iter_num = 3;
    size_t ode_discretisation = 4;

    std::string global_time = "tau";
    std::string sample_time = "counter";
    double noise_var = 1;

    //Used by translator
    bool decompose = false;

    struct ctrl
    {
        std::string sys_out;
        std::vector<std::string> plant_output;
        std::vector<std::string> controller_output;
        std::vector<std::string> controller_input;
        std::map<std::string, double> noise_variance;
    } controller;

} extern global_config;

void parse_pdrh_config(int, char**);
bool is_flag(char*);
bool is_pdrh(char*);
bool is_drh(char*);
void print_usage();
void print_version();

#endif //PROBREACH_PDRH_CONTEXT_H
