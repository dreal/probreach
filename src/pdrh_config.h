//
// Created by fedor on 24/02/16.
//

#ifndef PROBREACH_PDRH_CONTEXT_H
#define PROBREACH_PDRH_CONTEXT_H
#include "pugixml.hpp"

struct pdrh_config
{
    // verified integration options
    double integral_inf_coeff = 1e-01;
    double integral_pdf_step = 1e-01;
    // solver options
    std::string solver_bin = "dReal";
    std::string solver_opt = "";
    // algorithm options
    double precision_prob = 1e-03;
    double precision_prob_single = 1e-03;
    double precision_nondet = 1e-03;
    bool partition_prob = false;
    bool partition_nondet = false;
    double solver_precision_ratio = 1e-03;
    unsigned int solver_timeout = 10; // seconds
    int reach_depth_min = 0;
    int reach_depth_max = 0;
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
    long int sample_size = 1;
    bool sample_flag = false;
    double chernoff_acc = 1e-2;
    double chernoff_conf = 0.99;
    bool chernoff_flag = false;
    bool delta_sat = false;
} extern global_config;

void parse_pdrh_config(int, char**);
void print_usage();
void print_version();

#endif //PROBREACH_PDRH_CONTEXT_H
