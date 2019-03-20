//
// Created by fedor on 03/03/16.
//

#include <gsl/gsl_rng.h>
#include <gsl/gsl_qrng.h>
#include <gsl/gsl_cdf.h>
#include <capd/intervals/lib.h>
#include "mc.h"
#include "easylogging++.h"
#include "pdrh_config.h"
#include "measure.h"
#include "box_factory.h"
#include <chrono>
#include <iomanip>
#include <omp.h>
#include "rnd.h"
#include "ap.h"
#include "pdrh2box.h"
#include "naive.h"

using namespace std;

capd::interval algorithm::evaluate_pha_chernoff(int min_depth, int max_depth, double acc, double conf, vector<box> nondet_boxes) {
    const gsl_rng_type *T;
    gsl_rng *r;
    gsl_rng_env_setup();
    T = gsl_rng_default;
    // creating random generator
    r = gsl_rng_alloc(T);
    // setting the seed
    gsl_rng_set(r, std::chrono::system_clock::now().time_since_epoch() / std::chrono::milliseconds(1));
    // getting sample size using the Chernoff bound formula
    long int sample_size = (long int) std::ceil((1 / (2 * acc * acc)) * std::log(2 / (1 - conf)));
//    long int sample_size = algorithm::get_cernoff_bound(acc, std::sqrt(conf));
    long int sat = 0;
    long int unsat = 0;
    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Chernoff-Hoeffding algorithm started";
    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Random sample size: " << sample_size;
#pragma omp parallel for schedule (dynamic)
    for (long int ctr = 0; ctr < sample_size; ctr++)
    {
        // getting all paths
        std::vector<std::vector<pdrh::mode *>> paths = pdrh::get_all_paths(min_depth, max_depth);
//        // getting all paths
//        for (pdrh::state i : pdrh::init) {
//            for (pdrh::state g : pdrh::goal) {
//                for (int j = min_depth; j <= max_depth; j++) {
//                    std::vector<std::vector<pdrh::mode *>> paths_j = pdrh::get_paths(pdrh::get_mode(i.id),
//                                                                                     pdrh::get_mode(g.id), j);
//                    paths.insert(paths.cend(), paths_j.cbegin(), paths_j.cend());
//                }
//            }
//        }
        // getting a sample
        box b = rnd::get_random_sample(r);
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Random sample: " << b;
        std::vector<box> boxes = {b};
        boxes.insert(boxes.end(), nondet_boxes.begin(), nondet_boxes.end());
        int undet_counter = 0;
        bool sat_flag = false;
        // evaluating all paths
        for (std::vector<pdrh::mode *> path : paths) {
            std::stringstream p_stream;
            for (pdrh::mode *m : path) {
                p_stream << m->id << " ";
            }
            // removing trailing whitespace
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Path: " << p_stream.str().substr(0, p_stream.str().find_last_of(" "));
            int res;
            if (global_config.delta_sat)
            {
                res = decision_procedure::evaluate_delta_sat(path, boxes, global_config.solver_bin, global_config.solver_opt);
            }
            else
            {
                res = decision_procedure::evaluate(path, boxes, global_config.solver_bin, global_config.solver_opt);
            }
#pragma omp critical
            {
                if (res == decision_procedure::SAT)
                {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                    sat++;
                    sat_flag = true;
                } else if (res == decision_procedure::UNSAT)
                {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                } else if (res == decision_procedure::UNDET)
                {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDET";
                    //cout<< "Undet sample: " << b << endl;
                    //exit(EXIT_FAILURE);
                    undet_counter++;
                }
            }
            if (sat_flag) {
                break;
            }
        }
        // updating unsat counter
#pragma omp critical
        {
            if ((undet_counter == 0) && (!sat_flag)) {
                unsat++;
            }
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "CI: " << capd::interval(
                        ((double) sat / (double) sample_size) - acc,
                        ((double) (sample_size - unsat) / (double) sample_size) + acc);
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Progress: " << (double) ctr / (double) sample_size;
        }
    }
    gsl_rng_free(r);
    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Chernoff-Hoeffding algorithm finished";
    return capd::interval(((double) sat / (double) sample_size) - acc,
                          ((double) (sample_size - unsat) / (double) sample_size) + acc);
}

capd::interval algorithm::evaluate_pha_bayesian(int min_depth, int max_depth, double acc, double conf, vector<box> nondet_boxes) {
    const gsl_rng_type *T;
    gsl_rng *r;
    gsl_rng_env_setup();
    T = gsl_rng_default;
    // creating random generator
    r = gsl_rng_alloc(T);
    // setting the seed
    gsl_rng_set(r, std::chrono::system_clock::now().time_since_epoch() / std::chrono::milliseconds(1));

    // getting sample size with recalculated confidence
    long int sample_size = 0;
    long int sat = 0;
    long int unsat = 0;
    // parameters of the beta distribution
    double alpha = 1;
    double beta = 1;
    // initializing posterior mean
    double post_mean_sat = ((double) sat + alpha) / ((double) sample_size + alpha + beta);
    double post_mean_unsat = ((double) sample_size - unsat + alpha) / ((double) sample_size + alpha + beta);
    double post_prob = 0;
    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Bayesian estimations algorithm started";
    // getting set of all paths
    //std::vector<std::vector<pdrh::mode *>> paths = pdrh::get_paths();
    #pragma omp parallel
    while (post_prob < conf)
    {
        // getting a sample
        box b = rnd::get_random_sample(r);
        // increasing the sample size
        #pragma omp critical
        {
            sample_size++;
        }
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Random sample: " << b;
        std::vector<box> boxes = {b};
        boxes.insert(boxes.end(), nondet_boxes.begin(), nondet_boxes.end());

        int timeout_counter = 0;
        // checking solver type
//        if (global_config.solver_type == solver::type::DREAL)
//        {
        // evaluating all paths
//        vector<vector<pdrh::mode *>> paths = ap::get_all_paths(boxes);
        int res = decision_procedure::UNDET;
        // checking what verification method is chosen
//            int sim_res = ap::simulate(boxes);
//            int ver_res = ap::verify(boxes);
//            if(sim_res != ver_res)
//            {
//                cout << "Sim: " << sim_res << " Ver: " << ver_res << " Boxes:" << endl;
//                for(box b : boxes)
//                {
//                    cout << b << endl;
//                }
//                exit(EXIT_FAILURE);
//            }

        if (global_config.use_verified)
        {
            //res = decision_procedure::evaluate(paths, boxes, dreal::solver_bin, "");
            res = ap::verify(min_depth, max_depth, boxes);
            //res = ap::simulate_path(ap::get_all_paths(boxes).front(), ap::init_to_box(boxes), boxes);
        }
        else
        {
            res = ap::simulate(min_depth, max_depth, boxes);
//                // computing maximum robustness for the set of paths
//                capd::interval rob = ap::compute_max_robustness(paths, ap::init_to_box(boxes), boxes);
//                if(rob.leftBound() > 0)
//                {
//                    res = decision_procedure::SAT;
//                }
//                else if(rob.rightBound() < 0)
//                {
//                    res = decision_procedure::UNSAT;
//                }
        }
        // updating the counters
        #pragma omp critical
        {
            switch (res)
            {
                case decision_procedure::SAT:
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                    sat++;
                    break;

                case decision_procedure::UNSAT:
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                    unsat++;
                    //ap::unsat_samples.push_back(b);
                    break;

                case decision_procedure::UNDET:
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDET";
                    break;
            }
        }
//        }
//        else if (global_config.solver_type == solver::type::ISAT)
//        {
//            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Evaluating with iSAT:";
//            int res = decision_procedure::evaluate_isat(boxes);
//            if (res == decision_procedure::SAT)
//            {
//                CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
//                sat++;
//            } else if (res == decision_procedure::UNSAT)
//            {
//                CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
//                unsat++;
//                ap::unsat_samples.push_back(b);
//            }
//        }
//        else
//        {
//            stringstream s;
//            s << "Unrecognized solver";
//            throw runtime_error(s.str().c_str());
//        }
        // updating unsat counter
        #pragma omp critical
        {
            post_mean_sat = ((double) sat + alpha) / ((double) sample_size + alpha + beta);
            post_mean_unsat = ((double) sample_size - unsat + alpha) / ((double) sample_size + alpha + beta);
            if (post_mean_sat >= acc) {
                post_prob = gsl_cdf_beta_P(post_mean_unsat + acc, sample_size - unsat + alpha, unsat + beta)
                            - gsl_cdf_beta_P(post_mean_sat - acc, sat + alpha, sample_size - sat + beta);
            } else {
                post_prob = gsl_cdf_beta_P(post_mean_unsat + acc, sample_size - unsat + alpha, unsat + beta)
                            - gsl_cdf_beta_P(0, sat + alpha, sample_size - sat + beta);
            }
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "CI: " << capd::interval(max(post_mean_sat - acc, 0.0),
                                                                                          min(post_mean_unsat + acc,
                                                                                              1.0));
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "P(SAT) mean: " << post_mean_sat;
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "P(UNSAT) mean: " << post_mean_unsat;
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Random sample size: " << sample_size;
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "P prob: " << post_prob;
        }
    }
    gsl_rng_free(r);
    // displaying sample size if enabled
    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Random sample size: " << sample_size;
    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Bayesian estimations algorithm finished";
    return capd::interval(max(post_mean_sat - acc, 0.0), min(post_mean_unsat + acc, 1.0));
}

pair<box, capd::interval> algorithm::evaluate_npha_sobol(int min_depth, int max_depth, int size) {
    gsl_qrng *q = gsl_qrng_alloc(gsl_qrng_sobol, pdrh::par_map.size());

    //initializing probability value
    pair<box, capd::interval> res;
    if (global_config.max_prob) {
        res = make_pair(box(), capd::interval(0.0));
    } else {
        res = make_pair(box(), capd::interval(1.0));
    }
    box domain = pdrh2box::get_nondet_domain();
    vector<pair<box, capd::interval>> samples;
    while (domain.max_side_width() > global_config.sobol_term_arg) {
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Explored space: " << domain << " | "
                                                                 << domain.max_side_width();
        for (int i = 0; i < size; i++) {
            box b = rnd::get_sobol_sample(q, domain);
            CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Quasi-random sample: " << b;
            capd::interval probability;
            if (global_config.bayesian_flag) {
                probability = evaluate_pha_bayesian(min_depth, max_depth, global_config.bayesian_acc,
                                                    global_config.bayesian_conf, vector<box>{b});
            } else if (global_config.chernoff_flag) {
                probability = evaluate_pha_chernoff(min_depth, max_depth, global_config.chernoff_acc,
                                                    global_config.chernoff_conf, vector<box>{b});
            } else {
                CLOG(ERROR, "algorithm") << "Unknown setting";
                exit(EXIT_FAILURE);
            }
            // fixing probability value
            if (probability.leftBound() < 0) {
                probability.setLeftBound(0);
            }
            if (probability.rightBound() > 1) {
                probability.setRightBound(1);
            }
            CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Probability: " << probability << endl;
            samples.push_back(make_pair(b, probability));
        }
        if (global_config.max_prob) {
            sort(samples.begin(), samples.end(), measure::compare_pairs::descending);
        } else {
            sort(samples.begin(), samples.end(), measure::compare_pairs::ascending);
        }
        vector<pair<box, capd::interval>> elite;
        copy_n(samples.begin(), ceil(samples.size() * global_config.elite_ratio), back_inserter(elite));
        vector<box> elite_boxes;
        for (pair<box, capd::interval> p : elite) {
            elite_boxes.push_back(p.first);
        }
        res = samples.front();
        samples.clear();
        domain = box_factory::get_cover(elite_boxes);
    }
    gsl_qrng_free(q);
    return res;
}

pair<box, capd::interval> algorithm::evaluate_npha_cross_entropy_normal(size_t min_depth, size_t max_depth, size_t size,
                                                                            size_t iter_num, double acc, double conf)
{
    // random number generator for cross entropy
    const gsl_rng_type *T;
    gsl_rng *r;
    gsl_rng_env_setup();
    T = gsl_rng_default;
    // creating random generator
    r = gsl_rng_alloc(T);
    // setting the seed
    gsl_rng_set(r, std::chrono::system_clock::now().time_since_epoch() / std::chrono::milliseconds(1));
    box domain = pdrh2box::get_nondet_domain();
    //initializing probability value
    pair<box, capd::interval> res(domain, capd::interval(0.0));
    if (global_config.min_prob) res = make_pair(domain, capd::interval(1.0));
    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Domain of nondeterministic parameters: " << domain;
    box mean = domain.get_mean();
    box sigma = domain.get_stddev();
    box var = sigma * sigma;
    vector<pair<box, capd::interval>> samples;
    capd::interval size_correction_coef(1e-32);
    // getting initial mode
    pdrh::mode *init_mode = pdrh::get_mode(pdrh::init.front().id);
    //#pragma omp parallel
    for (int j = 0; j < iter_num; j++)
    {
        var = sigma * sigma;
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Iteration number: " << j + 1;
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Mean: " << mean;
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Standard deviation: " << sigma;
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Variance: " << var;
        // correct the sample size only if the probability of sampling outside the domain is still greater than 0.99999
        if (size_correction_coef.leftBound() < 0.99999)
        {
            size_correction_coef = measure::get_sample_prob(domain, mean, sigma);
        }
        unsigned long new_size = (unsigned long) ceil(size / size_correction_coef.leftBound());
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Sample size: " << new_size;
        int outliers = 0;
        //#pragma omp parallel for
        for (int i = 0; i < new_size; i++)
        {
            box b = rnd::get_normal_random_sample(r, mean, sigma);
            CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Quasi-random sample: " << b;
            capd::interval probability;
            if (domain.contains(b)) {
                CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "The sample is inside the domain";
                // stability test
//                if(stability::is_stable(init_mode->odes, pdrh::node_to_interval(init_mode->time.second).rightBound(), ap::init_to_box({}), b))
                if (true) {
//                    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "The sample is stable";
                    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Stability check is switched off";
                    if (global_config.bayesian_flag) {
                        probability = evaluate_pha_bayesian(min_depth, max_depth, acc, conf, vector<box>{b});
                    } else if (global_config.chernoff_flag) {
                        probability = evaluate_pha_chernoff(min_depth, max_depth, acc, conf, vector<box>{b});
                    } else {
                        CLOG(ERROR, "algorithm") << "Unknown setting";
                        exit(EXIT_FAILURE);
                    }
                    // fixing probability value
                    if (probability.leftBound() < 0) {
                        probability.setLeftBound(0);
                    }
                    if (probability.rightBound() > 1) {
                        probability.setRightBound(1);
                    }
                } else {
                    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "The sample is unstable";
                }
            } else {
                CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "The sample is outside the domain";
                outliers++;
                if (global_config.max_prob) {
                    probability = capd::interval(-numeric_limits<double>::infinity());
                } else {
                    probability = capd::interval(numeric_limits<double>::infinity());
                }
            }
            CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Probability: " << probability << endl;
            samples.push_back(make_pair(b, probability));
        }
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Number of outliers: " << outliers << endl;
        if (global_config.max_prob) {
            sort(samples.begin(), samples.end(), measure::compare_pairs::descending);
        } else {
            sort(samples.begin(), samples.end(), measure::compare_pairs::ascending);
        }
        vector<pair<box, capd::interval>> elite;
        copy_n(samples.begin(), ceil(samples.size() * global_config.elite_ratio), back_inserter(elite));
        // getting elite boxes
        vector<box> elite_boxes;
        for (pair<box, capd::interval> p : elite) {
            elite_boxes.push_back(p.first);
        }
        // updating resulting probability
        if (global_config.min_prob) {
            if (samples.front().second.mid().leftBound() < res.second.mid().leftBound()) {
                res = samples.front();
            }
        } else {
            if (samples.front().second.mid().leftBound() > res.second.mid().leftBound()) {
                res = samples.front();
            }
        }
        samples.clear();
        mean = box_factory::get_mean(elite_boxes);
        sigma = box_factory::get_stddev(elite_boxes);
    }
    gsl_rng_free(r);
    return res;
}

pair<box, capd::interval> algorithm::evaluate_npha_cross_entropy_beta(int min_depth, int max_depth, int size) {
    // random number generator for cross entropy
    const gsl_rng_type *T;
    gsl_rng *r;
    gsl_rng_env_setup();
    T = gsl_rng_default;
    // creating random generator
    r = gsl_rng_alloc(T);
    // setting the seed
    gsl_rng_set(r, std::chrono::system_clock::now().time_since_epoch() / std::chrono::milliseconds(1));
    //initializing probability value
    pair<box, capd::interval> res;
    box domain = pdrh2box::get_nondet_domain();
    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Domain of nondeterministic parameters: " << domain;
    map<string, capd::interval> one_map, two_map, d_map, half_map;
    d_map = domain.get_map();
    for (auto it = d_map.cbegin(); it != d_map.cend(); it++) {
        one_map.insert(make_pair(it->first, capd::interval(1.0)));
        two_map.insert(make_pair(it->first, capd::interval(2.0)));
    }
    box alpha(one_map), beta(one_map), one(one_map), two(two_map);
    //box mode = box_factory::map_box(two, domain);
    //box old_mode = mode;
    box var = (alpha * beta) / ((alpha + beta) * (alpha + beta) * (alpha + beta + one));
    //int term_counter = 0;
    vector<pair<box, capd::interval>> samples;
    //#pragma omp parallel
    while (var.max_coordinate_value() > global_config.cross_entropy_term_arg) {
        var = (alpha * beta) / ((alpha + beta) * (alpha + beta) * (alpha + beta + one));
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Alpha: " << alpha;
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Beta: " << beta;
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Variance: " << var;
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Sample size: " << size;
        //#pragma omp parallel for
        for (int i = 0; i < size; i++) {
            box b = rnd::get_beta_random_sample(r, alpha, beta, domain);
            CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Quasi-random sample: " << b;
            capd::interval probability;
            CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "The sample is inside the domain";
            if (global_config.bayesian_flag) {
                probability = evaluate_pha_bayesian(min_depth, max_depth, global_config.bayesian_acc,
                                                    global_config.bayesian_conf, vector<box>{b});
            } else if (global_config.chernoff_flag) {
                probability = evaluate_pha_chernoff(min_depth, max_depth, global_config.chernoff_acc,
                                                    global_config.chernoff_conf, vector<box>{b});
            } else {
                CLOG(ERROR, "algorithm") << "Unknown setting";
                exit(EXIT_FAILURE);
            }
            // fixing probability value
            if (probability.leftBound() < 0) {
                probability.setLeftBound(0);
            }
            if (probability.rightBound() > 1) {
                probability.setRightBound(1);
            }
            CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Probability: " << probability << endl;
            samples.push_back(make_pair(b, probability));
        }
        if (global_config.max_prob) {
            sort(samples.begin(), samples.end(), measure::compare_pairs::descending);
        } else {
            sort(samples.begin(), samples.end(), measure::compare_pairs::ascending);
        }
        vector<pair<box, capd::interval>> elite;
        copy_n(samples.begin(), ceil(samples.size() * global_config.elite_ratio), back_inserter(elite));
        vector<box> elite_boxes;
        for (pair<box, capd::interval> p : elite) {
            elite_boxes.push_back(p.first);
        }
        cout << "Number of elite samples: " << elite_boxes.size() << endl;
        res = samples.front();
        samples.clear();
        pair<box, box> beta_params = rnd::update_beta_dist(elite_boxes, domain, alpha, beta);
        alpha = beta_params.first;
        beta = beta_params.second;
    }
    gsl_rng_free(r);
    return res;
}
























