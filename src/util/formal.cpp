//
// Created by fedor on 12/02/19.
// Modified by Jevgenij on 13/04/22
//

#include <capd/intervals/lib.h>
#include "easylogging++.h"
#include "pdrh_config.h"
#include "measure.h"
#include "box_factory.h"
#include <iomanip>
#include "pdrh2box.h"
#include "formal.h"
#include "decision_procedure.h"


int formal::evaluate_ha(int min_depth, int max_depth)
{
    vector<vector<pdrh::mode *>> paths = pdrh::get_all_paths(min_depth, max_depth);
    return decision_procedure::evaluate(paths, {}, global_config.solver_bin, global_config.solver_opt);
}

capd::interval formal::evaluate_pha(int min_depth, int max_depth)
{
    short s_count = 0, un_count = 0, und_count = 0, stack_update = 0;
    CLOG_IF(global_config.verbose, INFO, "algorithm") << setprecision(16);
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Obtaining partition of domain of continuous random parameters";
    std::vector<box> init_rv_partition = measure::get_rv_partition(); // getting partition of domain of continuous random variables
    box rv_domain = measure::bounds::get_rv_domain();   // getting domain of continuous random variables
    if (!global_config.partition_prob) { // here we start with entire domain instead of partition
        init_rv_partition.clear();
        init_rv_partition.push_back(rv_domain);
    }

    std::vector<box> dd_partition = measure::get_dd_partition(); // getting partition of domain of discrete random variables
    if (dd_partition.empty()) {
        dd_partition.emplace_back();
    }
    capd::interval probability(0, 1);

    // checking if there are any continuous random variables
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << probability;

    // generating all paths of lengths [min_depth, max_depth]
    std::vector<std::vector<pdrh::mode *>> paths = pdrh::get_all_paths(min_depth, max_depth);

    //resulting probability
    capd::interval res_prob(0.0);

    // evaluating boxes
    for (const box& dd : dd_partition)
    {
        if (!pdrh::rv_map.empty())
            probability = capd::interval(0, 2 -
                            measure::p_measure(rv_domain, global_config.precision_prob).leftBound());
        vector<box> rv_partition = init_rv_partition;
        std::vector<box> rv_stack;

        while (capd::intervals::width(probability) > global_config.precision_prob)
        {
            // sorting boxes by probability value
            if (global_config.sort_rv_flag)
            {
                CLOG_IF(global_config.verbose, INFO, "algorithm")
                    << "Sorting the partition of domain of continuous random parameters";
                sort(rv_partition.begin(), rv_partition.end(), measure::compare_boxes_by_p_measure);
            }

            // Added default and shared attr
            #pragma omp parallel for default(none) shared(rv_partition, global_config, dd, paths, probability, rv_stack, s_count, un_count, und_count)
            for (const auto& rv : rv_partition)
            {
                // calculating probability measure of the box
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "\n====================";
                capd::interval p_box(1);
                if (!dd.empty())
                {
                    p_box *= measure::p_dd_measure(dd);
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "dd_box: " << dd;
                }
                if (!rv.empty())
                {
                    p_box *= measure::p_measure(rv, global_config.precision_prob);
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "rv_box: " << rv;
                }
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "p_box: " << p_box;

                // evaluating boxes
                std::vector<box> boxes{dd, rv};

                // undetermined answers counter
                int undet_counter = 0;

                // unsat counter
                int unsat_counter = 0;

                // sat flag
                bool sat_flag = false;

                // evaluating all paths for all dd and rv
                for (const std::vector<pdrh::mode *>& path : paths) {
                    std::string solver_opt;
                    std::stringstream p_stream;
                    for (pdrh::mode *m : path) {
                        p_stream << m->id << " ";
                    }
                    // removing trailing whitespace
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Path: " << p_stream.str().substr(0,
                                                                                                           p_stream.str().find_last_of(
                                                                                                                   ' '));
                    std::stringstream s;

                    // changing solver precision
                    #pragma omp critical
                    {
                        solver_opt = global_config.solver_opt;
                        s << solver_opt << " --precision " <<
                          measure::volume(rv).leftBound() * global_config.solver_precision_ratio;
                        global_config.solver_opt = s.str();
                    }
                    int res = decision_procedure::evaluate(path, boxes, global_config.solver_bin, s.str());

                    #pragma omp critical
                    {
                        global_config.solver_opt = solver_opt;
                        switch (res)
                        {
                            case decision_procedure::result::SAT:
                                s_count++;
                                if (p_box.leftBound() > 0) {
                                    probability = capd::interval(probability.leftBound() + p_box.leftBound(),
                                                                 probability.rightBound());
                                }
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << probability;
                                sat_flag = true;
                                break;

                            case decision_procedure::result::UNSAT:
                                un_count++;
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                                unsat_counter++;
                                break;
                            case decision_procedure::result::UNDET:
                                und_count++;
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDET";
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << probability;
                                undet_counter++;
                                break;
                            case decision_procedure::result::ERROR:
                                CLOG(ERROR, "algorithm") << "Error occurred while calling the solver";
                                exit(EXIT_FAILURE);

                            default:
                                break;
                        }
                    }
                    // breaking out of the loop if a sat path was found
                    break;
                }
                #pragma omp critical
                {
                    // checking if there are no sat answers
                    if (!sat_flag)
                    {
                        // if the box is undetermined on either path
                        if (undet_counter > 0)
                        {
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Bisect " << rv;
                            std::vector<box> rv_bisect = box_factory::bisect(rv);
                            ulong init_stack_size = rv_stack.size();
                            rv_stack.insert(rv_stack.end(), rv_bisect.begin(), rv_bisect.end());
                        }
                            // if the box is unsat for all paths
                        else if (unsat_counter == paths.size())
                        {
                            if (p_box.rightBound() > 0) {
                                probability = capd::interval(probability.leftBound(),
                                                             probability.rightBound() - p_box.leftBound());
                            }
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << probability;
                        }
                    }
                }

            }

            // copying the bisected boxes from the stack to partition
            rv_partition = rv_stack;
            rv_stack.clear();

            // breaking out of the loop if there are no continuous random variables
            if (pdrh::rv_map.empty())
            {
                rv_partition.emplace_back();
                break;
            }
        }
        if (!dd.empty())
        {
            capd::interval dd_measure = measure::p_dd_measure(dd);
            res_prob += probability * dd_measure;
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "P(" << dd << ") = " << probability * dd_measure;
        }
        else
        {
            res_prob = probability;
        }

    }
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT answers: " << s_count;
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT answers: " << un_count;
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDET answers: " << und_count;
    return res_prob;
}

std::map<box, capd::interval> formal::evaluate_npha(int min_depth, int max_depth) {
    CLOG_IF(global_config.verbose, INFO, "algorithm") << setprecision(16);
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Obtaining domain of nondeterministic parameters";
    // getting parameter domain
    box nd_domain = pdrh2box::get_nondet_domain();
    // initially partition is the entire parameter domain
    std::vector<box> nd_partition{nd_domain};
    // if flag is enabled the domain is partitioned up to precision_nondet
    if (global_config.partition_nondet) {
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Obtaining partition of nondeterministic domain";
        nd_partition.clear();
        //nd_partition = box_factory::partition(nd_domain, global_config.precision_nondet);
        nd_partition = box_factory::partition(nd_domain, global_config.partition_nondet_map);
    }
    // getting partition of domain of continuous random variables
    CLOG_IF(global_config.verbose, INFO, "algorithm")
        << "Obtaining partition of domain of continuous random parameters";
    std::vector<box> rv_partition = measure::get_rv_partition();
    if (rv_partition.empty()) {
        rv_partition.emplace_back();
    }
    // getting domain of continuous random variables
    box rv_domain = measure::bounds::get_rv_domain();
    // here we start with entire domain instead of partition
    if (!global_config.partition_prob) {
        rv_partition.clear();
        rv_partition.push_back(rv_domain);
    }
        // performing extra partition if the probability partition map is defined
    else {
        vector<box> tmp_vector;
        for (const box& b: rv_partition) {
            vector<box> extra_partition = box_factory::partition(b, global_config.partition_prob_map);
            tmp_vector.insert(tmp_vector.cend(), extra_partition.cbegin(), extra_partition.cend());
        }
        rv_partition = tmp_vector;
    }
    // sorting boxes by probability value
    if (global_config.sort_rv_flag) {
        CLOG_IF(global_config.verbose, INFO, "algorithm")
            << "Sorting the partition of domain of continuous random parameters";
        sort(rv_partition.begin(), rv_partition.end(), measure::compare_boxes_by_p_measure);
    }

    // getting partition of domain of discrete random variables
    std::vector<box> dd_partition = measure::get_dd_partition();
    // fix for now
    if (dd_partition.empty()) {
        dd_partition.emplace_back();
    }
    // generating all paths of lengths [min_depth, max_depth]
    std::vector<std::vector<pdrh::mode *>> paths = pdrh::get_all_paths(min_depth, max_depth);
    // initializing probability map
    std::map<box, capd::interval> p_map;
    capd::interval total_probability = capd::interval(0, 2 - measure::p_measure(rv_domain,
                                                                                global_config.precision_prob).leftBound());
    for (const box& nd: nd_partition) {
        p_map.insert(std::make_pair(nd, total_probability));
    }
    // initializing partition map
    std::map<box, std::vector<box>> partition_map;
    for (const box& nd: nd_partition) {
        partition_map.insert(std::make_pair(nd, rv_partition));
    }
    vector<box> total_partition = rv_partition;
    std::map<box, capd::interval> res_map, final_map;
    for (auto & it : p_map) {
        res_map.insert(make_pair(it.first, capd::interval(0.0)));
        final_map.insert(make_pair(it.first, capd::interval(0.0)));
    }
    // algorithm
    for (const box& dd: dd_partition) {
        // calculating the discrete measure
        capd::interval dd_measure(1.0);
        if (!dd.empty()) {
            dd_measure = measure::p_dd_measure(dd);
        }

        // probability map computation starts here
        while (!p_map.empty()) {
            // updating the nd_partition
            nd_partition.clear();
            for (const auto & it : p_map) {
                nd_partition.push_back(it.first);
            }
#pragma omp parallel  for schedule (dynamic) default(none) shared(nd_partition, rv_partition, partition_map, global_config, dd, paths, p_map, total_partition, res_map)
            for (const auto& nd : nd_partition) {

#pragma omp critical
                {
                    rv_partition = partition_map[nd];
                }

                vector<box> rv_stack;

                //#pragma omp parallel for schedule (dynamic)
                for (auto rv : rv_partition) {
                    // calculating probability measure of the box rv; initially p_box = [1.0, 1.0]
                    capd::interval p_box(1.0, 1.0);
#pragma omp critical
                    {
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "====================";
                        if (!nd.empty()) {
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "nd_box: " << nd;
                        }
                        if (!dd.empty()) {
                            //p_box *= measure::p_dd_measure(dd);
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "dd_box: " << dd;
                        }
                        if (!rv.empty()) {
                            p_box *= measure::p_measure(rv, global_config.precision_prob);
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "rv_box: " << rv;
                        }
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "p_box: " << p_box;
                    }
                    std::stringstream s;
                    std::string solver_opt;
#pragma omp critical
                    {
                        solver_opt = global_config.solver_opt;
                        s << solver_opt << " --precision ";
                        if (!rv.empty()) {
                            s << rv.min_side_width() * global_config.solver_precision_ratio;
                        } else {
                            s << global_config.solver_precision_ratio;
                        }
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Solver options: " << s.str();
                    }
                    switch (decision_procedure::evaluate(paths, vector<box>{nd, dd, rv}, global_config.solver_bin,
                                                         s.str())) {
                        case decision_procedure::result::SAT:
#pragma omp critical
                        {
                            if (p_box.leftBound() > 0) {
                                p_map[nd] = capd::interval(p_map[nd].leftBound() + p_box.leftBound(),
                                                           p_map[nd].rightBound());
                            }
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << p_map[nd];
                        }
                            break;

                        case decision_procedure::result::UNSAT:
#pragma omp critical
                        {
                            if (p_box.leftBound() > 0) {
                                p_map[nd] = capd::interval(p_map[nd].leftBound(),
                                                           p_map[nd].rightBound() - p_box.leftBound());
                            }
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << p_map[nd];
                        }
                            break;

                        case decision_procedure::result::UNDET:
#pragma omp critical
                        {
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDET";
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << p_map[nd];
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Bisect " << rv;
                            std::vector<box> rv_bisect = box_factory::bisect(rv);
                            rv_stack.insert(rv_stack.end(), rv_bisect.begin(), rv_bisect.end());
                            // updating total partition
                            auto it = find(total_partition.begin(), total_partition.end(), rv);
                            if (it != total_partition.end()) {
                                total_partition.erase(it);
                                total_partition.insert(total_partition.end(), rv_bisect.begin(), rv_bisect.end());
                            }
                        }
                            break;
                    }
                }
#pragma omp critical
                {
                    if (p_map.find(nd) == p_map.end()) {
                        CLOG(ERROR, "algorithm") << "The box " << nd << " is not in the map";
                        exit(EXIT_FAILURE);
                    }
                    capd::interval probability;
                    probability = p_map[nd];
                    if (capd::intervals::width(probability) <= global_config.precision_prob) {
                        CLOG_IF(global_config.verbose, INFO, "algorithm")
                            << "Epsilon is satisfied. Updating resulting probability map with " << nd;
                        p_map.erase(nd);
                        partition_map.erase(nd);
                        res_map[nd] = probability;// * dd_measure;
                    }
                    // sorting newly obtained boxes
                    if (global_config.sort_rv_flag) {
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Sorting bisected boxes";
                        sort(rv_stack.begin(), rv_stack.end(), measure::compare_boxes_by_p_measure);
                    }
                    // updating partition map only in case if probability value does not satisfy the probability precision
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Updating partition map";
                    if (partition_map.find(nd) != partition_map.cend()) {
                        partition_map[nd] = rv_stack;
                    }
                }
            }

            // updating probability and partition maps
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Updating probability map";
            std::map<box, capd::interval> tmp_map = p_map;
            for (const auto & it : tmp_map) {
                box nd = it.first;
                // checking if the system features nondeterministic parameters
                if (!nd.empty()) {
                    // bisecting the nondeterministic box
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Bisect " << nd;
                    std::vector<box> tmp_boxes;
                    // checking if the --ignore-nondet flag is up
                    if (global_config.ignore_nondet) {
                        tmp_boxes = box_factory::bisect(nd);
                    } else {
                        tmp_boxes = box_factory::bisect(nd, global_config.partition_nondet_map);
                    }
                    capd::interval tmp_prob_value = p_map[nd];
                    std::vector<box> tmp_rv_partition = partition_map[nd];
                    capd::interval tmp_final_prob_value = final_map[nd];
                    // removing probability and partition for the bisected box
                    p_map.erase(nd);
                    partition_map.erase(nd);
                    res_map.erase(nd);
                    final_map.erase(nd);
                    // updating probability and partition maps
                    if (tmp_boxes.size() > 1) {
                        for (const box& b: tmp_boxes) {
                            p_map.insert(make_pair(b, tmp_prob_value));
                            partition_map.insert(make_pair(b, tmp_rv_partition));
                            res_map.insert(make_pair(b, tmp_prob_value));
                            final_map.insert(make_pair(b, tmp_final_prob_value));
                        }
                    } else {
                        res_map.insert(make_pair(nd, tmp_prob_value));
                        final_map.insert(make_pair(nd, tmp_final_prob_value));
                    }
                }
            }
        }
        // probability map computation finishes here

        // multiplying every enclosure in the map by dd_measure
        for (auto it = final_map.begin(); it != final_map.end(); it++) {
            final_map[it->first] += res_map[it->first] * dd_measure;
        }
        // updating p_map and partition_map for the next iteration
        partition_map.clear();
        p_map.clear();
        res_map.clear();
        for (auto & it : final_map) {
            p_map.insert(make_pair(it.first, total_probability));
            res_map.insert(make_pair(it.first, capd::interval(0.0)));
            partition_map.insert(make_pair(it.first, total_partition));

        }
        return final_map;
    }
}
