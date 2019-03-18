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
//#include <solver/isat_wrapper.h>
#include "rnd.h"
#include "ap.h"
#include "pdrh2box.h"
#include "naive.h"
//#include "stability.h"

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
    // getting sample size with recalculated confidence
    long int sample_size = algorithm::get_cernoff_bound(acc, std::sqrt(conf));
    long int sat = 0;
    long int unsat = 0;
    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Chernoff-Hoeffding algorithm started";
    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Random sample size: " << sample_size;
#pragma omp parallel for schedule (dynamic)
    for (long int ctr = 0; ctr < sample_size; ctr++) {
        std::vector<std::vector<pdrh::mode *>> paths;
        // getting all paths
        for (pdrh::state i : pdrh::init) {
            for (pdrh::state g : pdrh::goal) {
                for (int j = min_depth; j <= max_depth; j++) {
                    std::vector<std::vector<pdrh::mode *>> paths_j = pdrh::get_paths(pdrh::get_mode(i.id),
                                                                                     pdrh::get_mode(g.id), j);
                    paths.insert(paths.cend(), paths_j.cbegin(), paths_j.cend());
                }
            }
        }
        // getting a sample
        box b = rnd::get_random_sample(r);
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Random sample: " << b;
        std::vector<box> boxes = {b};
        boxes.insert(boxes.end(), nondet_boxes.begin(), nondet_boxes.end());
        int undet_counter = 0;
        int timeout_counter = 0;
        bool sat_flag = false;
        // evaluating all paths
        for (std::vector<pdrh::mode *> path : paths) {
            std::stringstream p_stream;
            for (pdrh::mode *m : path) {
                p_stream << m->id << " ";
            }
            // removing trailing whitespace
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Path: " << p_stream.str().substr(0,
                                                                                                   p_stream.str().find_last_of(
                                                                                                           " "));
            int res;
            if (global_config.delta_sat) {
                res = decision_procedure::evaluate_delta_sat(path, boxes);
            } else {
                res = decision_procedure::evaluate(path, boxes);
            }
#pragma omp critical
            {
                if (res == decision_procedure::SAT) {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                    sat++;
                    sat_flag = true;
                } else if (res == decision_procedure::UNSAT) {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                } else if (res == decision_procedure::UNDET) {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDET";
                    //cout<< "Undet sample: " << b << endl;
                    //exit(EXIT_FAILURE);
                    undet_counter++;
                } else if (res == decision_procedure::ERROR) {
                    CLOG(ERROR, "algorithm") << "Error occured while calling a solver";
                    exit(EXIT_FAILURE);
                } else if (res == decision_procedure::SOLVER_TIMEOUT) {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "SOLVER_TIMEOUT";
                    timeout_counter++;
                }
            }
            if (sat_flag) {
                break;
            }
        }
        // updating unsat counter
#pragma omp critical
        {
            if ((undet_counter == 0) && (timeout_counter == 0) && (!sat_flag)) {
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
    while (post_prob < conf) {
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
            //res = decision_procedure::evaluate(paths, boxes, "");
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
            switch (res) {
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

                case decision_procedure::ERROR:
                    CLOG(ERROR, "algorithm") << "Error occured while calling a solver";
                    exit(EXIT_FAILURE);
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

capd::interval algorithm::evaluate_pha_chernoff(int min_depth, int max_depth, double acc, double conf) {
    return evaluate_pha_chernoff(min_depth, max_depth, acc, conf, vector<box>{});
}

capd::interval algorithm::evaluate_pha_bayesian(int min_depth, int max_depth, double acc, double conf) {
    return evaluate_pha_bayesian(min_depth, max_depth, acc, conf, vector<box>{});
}

long int algorithm::get_cernoff_bound(double acc, double conf) {
    if ((acc <= 0) || (conf < 0) || (conf >= 1)) {
        CLOG(ERROR, "algorithm") << "accuracy must be descending than 0 and confidence must be inside [0, 1) interval";
    }
    return (long int) std::ceil((1 / (2 * acc * acc)) * std::log(2 / (1 - conf)));
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

pair<capd::interval, box> algorithm::solve_min_max() {
    const gsl_rng_type *T;
    gsl_rng *r;
    gsl_rng_env_setup();
    T = gsl_rng_default;
    // creating random generator
    r = gsl_rng_alloc(T);
    // setting the seed
    gsl_rng_set(r, std::chrono::system_clock::now().time_since_epoch() / std::chrono::milliseconds(1));

    // the first element is the value of the objective function
    // the second element is the values of the nondet parameters
    std::map<capd::interval, box> rob_map;

    box nondet_domain = pdrh2box::get_nondet_domain();
    //initializing probability value
    box mean = nondet_domain.get_mean();
    box sigma = nondet_domain.get_stddev();
    box var = sigma * sigma;

    unsigned long sample_size = (unsigned long) ceil(
            global_config.sample_size / measure::get_sample_prob(nondet_domain, mean, sigma).rightBound());

    pair<capd::interval, box> res = make_pair(capd::interval(-numeric_limits<double>::max()), box());

#pragma omp parallel for
    for (int i = 0; i < sample_size; i++) {
        // taking a sample form the nondeterministic parameter space
        box nondet_box = rnd::get_normal_random_sample(r, mean, sigma);
        if (nondet_domain.contains(nondet_box)) {
            capd::interval rob(0);
            for (int j = 0; j < global_config.sample_size; j++) {
                //cout << "i = " << i << " j = " << j << endl;
                box random_box = rnd::get_random_sample(r);
                vector<vector<pdrh::mode *>> paths = ap::get_all_paths({nondet_box, random_box});
                // computing an objective function over a set of paths as an average value
                for (vector<pdrh::mode *> path : paths) {
                    capd::interval sample_rob = ap::compute_robustness(path, ap::init_to_box({nondet_box, random_box}),
                                                                       {nondet_box, random_box}) /
                                                (double) paths.size();
# pragma omp critical
                    {
                        rob = rob + sample_rob;
                    }
                }
            }
# pragma omp critical
            {
                // computing the statistical mean of the objective function
                rob = rob / global_config.sample_size;
                // updating the result here
                if (rob.leftBound() > res.first.rightBound()) {
                    res = make_pair(rob, nondet_box);
                }
                // adding to the list of objective functions
                rob_map.insert(make_pair(rob, nondet_box));
            }
        }
    }

    cout << "Means of robustness values:" << endl;
    for (auto it = rob_map.begin(); it != rob_map.end(); it++) {
        cout << it->first << " | " << it->second << endl;
    }

    gsl_rng_free(r);
    return res;
}

capd::interval algorithm::compute_robustness() {
    vector<vector<pdrh::mode *>> paths = ap::get_all_paths({});
    // computing an objective function over a set of paths as an average value
    capd::interval rob(-numeric_limits<double>::max());
    for (vector<pdrh::mode *> path : paths) {
        rob = ap::compute_robustness(path, ap::init_to_box({}), {});
    }
    return rob;
}


























