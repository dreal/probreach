//
// Created by fedor on 12/02/19.
//

#include <capd/intervals/lib.h>
#include "easylogging++.h"
#include "pdrh_config.h"
#include "measure.h"
#include "box_factory.h"
#include <iomanip>
#include <omp.h>
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
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Obtaining partition of domain of continuous random parameters";
    // getting partition of domain of continuous random variables
    std::vector<box> init_rv_partition = measure::get_rv_partition();
    // getting domain of continuous random variables
    box rv_domain = measure::bounds::get_rv_domain();
    // here we start with entire domain instead of partition
    if (!global_config.partition_prob) {
        init_rv_partition.clear();
        init_rv_partition.push_back(rv_domain);
    }
    // getting partition of domain of discrete random variables
    std::vector<box> dd_partition = measure::get_dd_partition();
    if (dd_partition.empty()) {
        dd_partition.push_back(box());
    }
    capd::interval probability(0, 1);
    // checking if there are any continuous random variables
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << probability;
    // generating all paths of lengths [min_depth, max_depth]
    std::vector<std::vector<pdrh::mode *>> paths = pdrh::get_all_paths(min_depth, max_depth);
    //resulting probability
    capd::interval res_prob(0.0);
    // evaluating boxes
    //#pragma omp parallel for
    for (box dd : dd_partition)
    {
        if (pdrh::rv_map.size() > 0) probability = capd::interval(0, 2 - measure::p_measure(rv_domain, global_config.precision_prob).leftBound());
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
            //for(box rv : rv_partition)
            #pragma omp parallel for
            for (size_t i = 0; i < rv_partition.size(); i++)
            {
                box rv = rv_partition.at(i);
                // calculating probability measure of the box
                // initially p_box = [1.0, 1.0]
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "====================";
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
                //cout << "Before evaluate loop " << omp_get_thread_num() << endl;
                for (std::vector<pdrh::mode *> path : paths) {
                    std::string solver_opt;
                    std::stringstream p_stream;
                    for (pdrh::mode *m : path) {
                        p_stream << m->id << " ";
                    }
                    // removing trailing whitespace
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Path: " << p_stream.str().substr(0,
                                                                                                           p_stream.str().find_last_of(
                                                                                                                   " "));
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
                    // setting old precision
                    #pragma omp critical
                    {
                        global_config.solver_opt = solver_opt;
                        switch (res)
                        {
                            case decision_procedure::SAT:
                                if (p_box.leftBound() > 0)
                                {
                                    probability = capd::interval(probability.leftBound() + p_box.leftBound(),
                                                                 probability.rightBound());
                                }
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << probability;
                                /*
                                if(capd::intervals::width(probability) <= global_config.precision_prob)
                                {
                                    return probability;
                                }
                                */
                                sat_flag = true;
                                break;

                            case decision_procedure::UNSAT:
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                                unsat_counter++;
                                break;
                            case decision_procedure::UNDET:
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDET";
                                undet_counter++;
                                break;
                            case decision_procedure::ERROR:
                                CLOG(ERROR, "algorithm") << "Error occurred while calling the solver";
                                exit(EXIT_FAILURE);

                            default:
                                break;
                        }
                    }
                    // breaking out of the loop if a sat path was found
                    if (sat_flag) break;
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
                            rv_stack.insert(rv_stack.end(), rv_bisect.begin(), rv_bisect.end());
                        }
                            // if the box is unsat for all paths
                        else if (unsat_counter == paths.size())
                        {
                            if (p_box.rightBound() > 0)
                            {
                                probability = capd::interval(probability.leftBound(),
                                                             probability.rightBound() - p_box.leftBound());
                            }
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << probability;
                        }
                    }
                };

            }
            // copying the bisected boxes from the stack to partition
            rv_partition = rv_stack;
            rv_stack.clear();
            // breaking out of the loop if there are no continuous random variables
            if (pdrh::rv_map.size() == 0)
            {
                rv_partition.push_back(box());
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
    return res_prob;
}

std::map<box, capd::interval> formal::evaluate_npha(int min_depth, int max_depth)
{
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
        rv_partition.push_back(box());
    }
    // getting domain of continuous random variables
    box rv_domain = measure::bounds::get_rv_domain();
    // here we start with entire domain instead of partition
    if (!global_config.partition_prob) {
        rv_partition.clear();
        rv_partition.push_back(rv_domain);
    }
    // performing extra partition if the probability partition map is defined
    else
    {
        //cout << "rv partition size before extra partition: " << rv_partition.size() << endl;
        vector<box> tmp_vector;
        for (box b : rv_partition)
        {
            vector<box> extra_partition = box_factory::partition(b, global_config.partition_prob_map);
            tmp_vector.insert(tmp_vector.cend(), extra_partition.cbegin(), extra_partition.cend());
        }
        rv_partition = tmp_vector;
        //cout << "rv partition size after extra partition:" << rv_partition.size() << endl;
    }
    // sorting boxes by probability value
    if (global_config.sort_rv_flag)
    {
        CLOG_IF(global_config.verbose, INFO, "algorithm")
            << "Sorting the partition of domain of continuous random parameters";
        sort(rv_partition.begin(), rv_partition.end(), measure::compare_boxes_by_p_measure);
    }

    // getting partition of domain of discrete random variables
    std::vector<box> dd_partition = measure::get_dd_partition();
    // fix for now
    if (dd_partition.empty())
    {
        dd_partition.push_back(box());
    }
    // generating all paths of lengths [min_depth, max_depth]
    std::vector<std::vector<pdrh::mode *>> paths = pdrh::get_all_paths(min_depth, max_depth);
    // initializing probability map
    std::map<box, capd::interval> p_map;
    capd::interval total_probability = capd::interval(0, 2 - measure::p_measure(rv_domain, global_config.precision_prob).leftBound());
    for (box nd : nd_partition) {
        p_map.insert(std::make_pair(nd, total_probability));
    }
    // initializing partition map
    std::map<box, std::vector<box>> partition_map;
    for (box nd : nd_partition) {
        partition_map.insert(std::make_pair(nd, rv_partition));
    }
    vector<box> total_partition = rv_partition;
    std::map<box, capd::interval> res_map, final_map;
    for (auto it = p_map.begin(); it != p_map.end(); it++) {
        res_map.insert(make_pair(it->first, capd::interval(0.0)));
        final_map.insert(make_pair(it->first, capd::interval(0.0)));
    }
    // algorithm
    for (box dd : dd_partition) {
        // calculating the discrete measure
        capd::interval dd_measure(1.0);
        if (!dd.empty()) {
            dd_measure = measure::p_dd_measure(dd);
        }

        // probability map computation starts here
        while (p_map.size() > 0) {
            // updating the nd_partition
            nd_partition.clear();
            //cout << "ND partition NOW:" << endl;
            for (auto it = p_map.cbegin(); it != p_map.cend(); it++) {
                nd_partition.push_back(it->first);
                //cout << it->first << endl;
            }
            // iterating through the boxes
            //for(box nd : nd_partition)
            #pragma omp parallel for schedule (dynamic)
            for (int j = 0; j < nd_partition.size(); j++) {
                box nd = nd_partition.at(j);

                #pragma omp critical
                {
                    rv_partition = partition_map[nd];
                }

                vector<box> rv_stack;

                //#pragma omp parallel for schedule (dynamic)
                for (int i = 0; i < rv_partition.size(); i++) {
                    box rv = rv_partition.at(i);
                    // calculating probability measure of the box rv; initally p_box = [1.0, 1.0]
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
                    switch (decision_procedure::evaluate(paths, vector<box>{nd, dd, rv}, global_config.solver_bin, s.str()))
                    {
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
                    //}
//                cout << "Probability map after " << nd << " was processed" << endl;
//                for(auto it2 = p_map.begin(); it2 != p_map.end(); it2++)
//                {
//                    std::cout << it2->first << " | " << it2->second << std::endl;
//                }
//                cout << "Resulting map after " << nd << " was processed" << endl;
//                for(auto it2 = res_map.begin(); it2 != res_map.end(); it2++)
//                {
//                    std::cout << it2->first << " | " << it2->second << std::endl;
//                }
//                cout << "----------------------------------" << endl;
                    //exit(EXIT_FAILURE);
                }
            }
//            cout << "----------------------------------" << endl;
//            cout << "Probability map after all boxes are processed" << endl;
//            for(auto it2 = p_map.begin(); it2 != p_map.end(); it2++)
//            {
//                std::cout << it2->first << " | " << it2->second << std::endl;
//            }
//            cout << "Resulting map after all boxes are processed" << endl;
//            for(auto it2 = res_map.begin(); it2 != res_map.end(); it2++)
//            {
//                std::cout << it2->first << " | " << it2->second << std::endl;
//            }
//            cout << "----------------------------------" << endl;
            //exit(EXIT_SUCCESS);

            // updating probability and partition maps
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Updating probability map";
            std::map<box, capd::interval> tmp_map = p_map;
            for (auto it = tmp_map.cbegin(); it != tmp_map.cend(); it++) {
                box nd = it->first;
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
                        for (box b : tmp_boxes) {
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
//            cout << "----------------------------------" << endl;
//            cout << "Probability map after it's been updated" << endl;
//            for(auto it2 = p_map.begin(); it2 != p_map.end(); it2++)
//            {
//                std::cout << it2->first << " | " << it2->second << std::endl;
//            }
//            cout << "Resulting map after it's been updated" << endl;
//            for(auto it2 = res_map.begin(); it2 != res_map.end(); it2++)
//            {
//                std::cout << it2->first << " | " << it2->second << std::endl;
//            }
//            cout << "----------------------------------" << endl;
        }
        // probability map computation finishes here

        // mutiplying every enclosure in the map by dd_measure
        for (auto it = final_map.begin(); it != final_map.end(); it++) {
            final_map[it->first] += res_map[it->first] * dd_measure;
        }

//        cout << "Final map after " << dd << endl;
//        for(auto it = final_map.begin(); it != final_map.end(); it++)
//        {
//            cout << it->first << " | " << it->second << endl;
//        }
//        cout << "----------------------------------" << endl;

        //return final_map;
        // multiplying every enclosure by probability measure of discrete parameter
//        for(auto it = res_map.begin(); it != res_map.end(); it++)
//        {
//            it->second *= measure::p_dd_measure(dd);
//        }
//        cout << "Resulting map before it's been multiplied by dd measure" << endl;
//        for(auto it2 = res_map.begin(); it2 != res_map.end(); it2++)
//        {
//            std::cout << it2->first << " | " << it2->second << std::endl;
//        }
//        cout << "----------------------------------" << endl;
        // updating p_map and partition_map for the next iteration
        partition_map.clear();
        p_map.clear();
        res_map.clear();
        for (auto it = final_map.begin(); it != final_map.end(); it++) {
            p_map.insert(make_pair(it->first, total_probability));
            res_map.insert(make_pair(it->first, capd::interval(0.0)));
            partition_map.insert(make_pair(it->first, total_partition));

        }
//        cout << "Total partition: " << endl;
//        for(box b : total_partition)
//        {
//            cout << b << endl;
//        }
//        exit(EXIT_FAILURE);
//        cout << "Updated probability map after the end of the loop" << endl;
//        for(auto it2 = p_map.begin(); it2 != p_map.end(); it2++)
//        {
//            std::cout << it2->first << " | " << it2->second << std::endl;
//        }
    }


    // cout << "Resulting map after adding" << endl;
    // for(auto it2 = res_map.begin(); it2 != res_map.end(); it2++)
    // {
    //     cout << it2->first << " | " << it2->second << std::endl;
    // }
    // cout << "Final p_map" << endl;
    // for(auto it2 = p_map.begin(); it2 != p_map.end(); it2++)
    // {
    //     cout << it2->first << " | " << it2->second << std::endl;
    // }
    return final_map;
}