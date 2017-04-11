//
// Created by fedor on 03/03/16.
//

#include <gsl/gsl_rng.h>
#include <gsl/gsl_qrng.h>
#include <gsl/gsl_cdf.h>
#include <capd/intervals/lib.h>
#include "algorithm.h"
#include "easylogging++.h"
#include "pdrh_config.h"
#include "measure.h"
#include "box_factory.h"
#include <chrono>
#include <iomanip>
#include <omp.h>
#include <solver/isat_wrapper.h>
#include "rnd.h"

decision_procedure::result algorithm::evaluate_ha(int depth)
{
    if(global_config.solver_type == solver::type::ISAT)
    {
        int res = decision_procedure::evaluate_isat(vector<box>{});
        if(res == decision_procedure::result::SAT)
        {
            return decision_procedure::result::SAT;
        }
        else if(res == decision_procedure::result::UNSAT)
        {
            return decision_procedure::result::UNSAT;
        }
    }
    else if(global_config.solver_type == solver::type::DREAL)
    {
        // generating all paths of lengths [min_depth, max_depth]
        std::vector<std::vector<pdrh::mode*>> paths;
        for(pdrh::state init : pdrh::init)
        {
            for (pdrh::state goal : pdrh::goal)
            {
                std::vector<std::vector<pdrh::mode *>> paths_i = pdrh::get_paths(pdrh::get_mode(init.id),
                                                                                 pdrh::get_mode(goal.id),
                                                                                 depth);
                paths.insert(paths.cend(), paths_i.cbegin(), paths_i.cend());
            }
        }
        switch(decision_procedure::evaluate(paths,{}, global_config.solver_opt))
        {
            case decision_procedure::result::SAT:
                return decision_procedure::result::SAT;

            case decision_procedure::result::UNSAT:
                return decision_procedure::result::UNSAT;

            case decision_procedure::result::UNDET:
                return decision_procedure::result::UNDET;
        }
    }
}

decision_procedure::result algorithm::evaluate_ha(int min_depth, int max_depth)
{
    int undet_counter = 0;
    for(int i = min_depth; i <= max_depth; i++)
    {
        decision_procedure::result res = algorithm::evaluate_ha(i);
        if(res == decision_procedure::SAT)
        {
            return res;
        }
        // never happens when --delta-sat is enabled
        else if(res == decision_procedure::UNDET)
        {
            undet_counter++;
        }
        else if(res == decision_procedure::ERROR)
        {
            return res;
        }
    }
    // checking if either of the paths was UNDET
    // never returned when --delta-sat is enabled
    if(undet_counter > 0)
    {
        return decision_procedure::UNDET;
    }
    return decision_procedure::UNSAT;
}

capd::interval algorithm::evaluate_pha(int min_depth, int max_depth)
{
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Obtaining partition of domain of continuous random parameters";
    // getting partition of domain of continuous random variables
    std::vector<box> init_rv_partition = measure::get_rv_partition();
    // getting domain of continuous random variables
    box rv_domain = measure::bounds::get_rv_domain();
    // here we start with entire domain instead of partition
    if(!global_config.partition_prob)
    {
        init_rv_partition.clear();
        init_rv_partition.push_back(rv_domain);
    }
    // getting partition of domain of discrete random variables
    std::vector<box> dd_partition = measure::get_dd_partition();
    if(dd_partition.empty())
    {
        dd_partition.push_back(box());
    }
    // checking if there are multiple initial and goal states
    if((pdrh::init.size() > 1) || (pdrh::goal.size() > 1))
    {
        CLOG(WARNING, "algorithm") << "Multiple initial or goal states are not supported";
    }
    capd::interval probability(0,1);
    // checking if there are any continuous random variables
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << std::scientific << probability;
    // generating all paths of lengths [min_depth, max_depth]
    std::vector<std::vector<pdrh::mode*>> paths;
    for(int i = min_depth; i <= max_depth; i++)
    {
        std::vector<std::vector<pdrh::mode*>> paths_i = pdrh::get_paths(pdrh::get_mode(pdrh::init.front().id), pdrh::get_mode(pdrh::goal.front().id), i);
        paths.insert(paths.cend(), paths_i.cbegin(), paths_i.cend());
    }
    //resulting probability
    capd::interval res_prob(0.0);
    // evaluating boxes
    //#pragma omp parallel for
    for(box dd : dd_partition)
    {
        if(pdrh::rv_map.size() > 0)
        {
            probability = capd::interval(0, 2 - measure::p_measure(rv_domain).leftBound());
        }
        vector<box> rv_partition = init_rv_partition;
        std::vector<box> rv_stack;
        while(capd::intervals::width(probability) > global_config.precision_prob)
        {
            //for(box rv : rv_partition)
            //#pragma omp parallel for
            for(unsigned long i = 0; i < rv_partition.size(); i++)
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
                    p_box *= measure::p_measure(rv);
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "rv_box: " << rv;
                }
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "p_box: " << p_box;
                // evaluating boxes
                std::vector<box> boxes{dd, rv};
                // undetermined answers counter
                int undet_counter = 0;
                // solver timeout counter
                int timeout_counter = 0;
                // unsat counter
                int unsat_counter = 0;
                // sat flag
                bool sat_flag = false;
                // evaluating all paths for all dd and rv
                //cout << "Before evaluate loop " << omp_get_thread_num() << endl;
                for (std::vector<pdrh::mode *> path : paths)
                {
                    std::string solver_opt;
                    std::stringstream p_stream;
                    for (pdrh::mode *m : path) {
                        p_stream << m->id << " ";
                    }
                    // removing trailing whitespace
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Path: " << p_stream.str().substr(0, p_stream.str().find_last_of(" "));
                    // changing solver precision
                    solver_opt = global_config.solver_opt;
                    std::stringstream s;
                    s << solver_opt << " --precision " <<
                    measure::volume(rv).leftBound() * global_config.solver_precision_ratio;
                    global_config.solver_opt = s.str();
                    int res = decision_procedure::evaluate(path, boxes);
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
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << std::scientific << probability;
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
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDEC";
                                undet_counter++;
                                break;
                            case decision_procedure::ERROR:
                                CLOG(ERROR, "algorithm") << "Error occurred while calling the solver";
                                exit(EXIT_FAILURE);
                                break;
                            case decision_procedure::SOLVER_TIMEOUT:
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "SOLVER_TIMEOUT";
                                timeout_counter++;
                                break;
                            default:
                                break;
                        }
                    }
                    // breaking out of the loop if a sat path was found
                    if(sat_flag)
                    {
                        break;
                    }
                }
                // checking if there are no sat answers
                if(!sat_flag)
                {
                    // if the box is undetermined on either path
                    if ((undet_counter > 0) || (timeout_counter > 0))
                    {
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Bisect " << std::scientific << rv;
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
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << std::scientific << probability;
                        /*
                        if (capd::intervals::width(probability) <= global_config.precision_prob)
                        {
                            return probability;
                        }
                        */
                    }
                }
                //cout << "P = " << probability << endl;
            }
            // copying the bisected boxes from the stack to partition
            rv_partition = rv_stack;
            rv_stack.clear();
            // breaking out of the loop if there are no continuous random variables
            if(pdrh::rv_map.size() == 0)
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

capd::interval algorithm::evaluate_pha(int depth)
{
    return algorithm::evaluate_pha(depth, depth);
}

std::map<box, capd::interval> algorithm::evaluate_npha(int min_depth, int max_depth)
{
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Obtaining domain of nondeterministic parameters";
    // getting parameter domain
    box nd_domain = pdrh::get_nondet_domain();
    // initially partition is the entire parameter domain
    std::vector<box> nd_partition { nd_domain };
    // if flag is enabled the domain is partitioned up to precision_nondet
    if(global_config.partition_nondet)
    {
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Obtaining partition of nondeterministic domain";
        nd_partition.clear();
        //nd_partition = box_factory::partition(nd_domain, global_config.precision_nondet);
        nd_partition = box_factory::partition(nd_domain, global_config.partition_nondet_map);
    }
    // getting partition of domain of continuous random variables
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Obtaining partition of domain of continuous random parameters";
    std::vector<box> rv_partition = measure::get_rv_partition();
    if(rv_partition.empty())
    {
        rv_partition.push_back(box());
    }
    // getting domain of continuous random variables
    box rv_domain = measure::bounds::get_rv_domain();
    // here we start with entire domain instead of partition
    if(!global_config.partition_prob)
    {
        rv_partition.clear();
        rv_partition.push_back(rv_domain);
    }
    // performing extra partition if the probability partition map is defined
    else
    {
        //cout << "rv partition size before extra partition: " << rv_partition.size() << endl;
        vector<box> tmp_vector;
        for(box b : rv_partition)
        {
            vector<box> extra_partition = box_factory::partition(b, global_config.partition_prob_map);
            tmp_vector.insert(tmp_vector.cend(), extra_partition.cbegin(), extra_partition.cend());
        }
        rv_partition = tmp_vector;
        //cout << "rv partition size after extra partition:" << rv_partition.size() << endl;
    }
    // sorting boxes by probability value
    if(global_config.sort_rv_flag)
    {
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Sorting the partition of domain of continuous random parameters";
        sort(rv_partition.begin(), rv_partition.end(), measure::compare_boxes_by_p_measure);
    }

    // getting partition of domain of discrete random variables
    std::vector<box> dd_partition = measure::get_dd_partition();
    // fix for now
    if(dd_partition.empty())
    {
        dd_partition.push_back(box());
    }
    // checking if there are multiple initial and goal states
    if((pdrh::init.size() > 1) || (pdrh::goal.size() > 1))
    {
        CLOG(WARNING, "algorithm") << "Multiple initial or goal states are not supported";
    }
    // generating all paths of lengths [min_depth, max_depth]
    std::vector<std::vector<pdrh::mode*>> paths;
    for(int i = min_depth; i <= max_depth; i++)
    {
        for(pdrh::state init : pdrh::init)
        {
            for (pdrh::state goal : pdrh::goal)
            {
                std::vector<std::vector<pdrh::mode *>> paths_i = pdrh::get_paths(pdrh::get_mode(init.id),
                                                                                 pdrh::get_mode(goal.id),
                                                                                 i);
                paths.insert(paths.cend(), paths_i.cbegin(), paths_i.cend());
            }
        }
    }
    // initializing probability map
    std::map<box, capd::interval> p_map;
    capd::interval total_probability = capd::interval(0, 2 - measure::p_measure(rv_domain).leftBound());
    for(box nd : nd_partition)
    {
        p_map.insert(std::make_pair(nd, total_probability));
    }
    // initializing partition map
    std::map<box, std::vector<box>> partition_map;
    for(box nd : nd_partition)
    {
        partition_map.insert(std::make_pair(nd, rv_partition));
    }
    vector<box> total_partition = rv_partition;

    std::map<box, capd::interval> res_map, final_map;

    for(auto it = p_map.begin(); it != p_map.end(); it++)
    {
        res_map.insert(make_pair(it->first, capd::interval(0.0)));
        final_map.insert(make_pair(it->first, capd::interval(0.0)));
    }

    // algorithm
    for(box dd : dd_partition)
    {
        // calculating the discrete measure
        capd::interval dd_measure(1.0);
        if(!dd.empty())
        {
            dd_measure = measure::p_dd_measure(dd);
        }

        // probability map computation starts here
        while(p_map.size() > 0)
        {
            // updating the nd_partition
            nd_partition.clear();
            //cout << "ND partition NOW:" << endl;
            for(auto it = p_map.cbegin(); it != p_map.cend(); it++)
            {
                nd_partition.push_back(it->first);
                //cout << it->first << endl;
            }
            // iterating through the boxes
            for(box nd : nd_partition)
            {
                rv_partition = partition_map[nd];
                vector<box> rv_stack;

                #pragma omp parallel for schedule (dynamic)
                for(int i = 0; i < rv_partition.size(); i++)
                {
                    box rv = rv_partition.at(i);
                    // calculating probability measure of the box rv; initally p_box = [1.0, 1.0]
                    capd::interval p_box(1.0,1.0);
                    #pragma omp critical
                    {
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "====================";
                        if(!nd.empty())
                        {
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "nd_box: " << nd;
                        }
                        if(!dd.empty())
                        {
                            //p_box *= measure::p_dd_measure(dd);
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "dd_box: " << dd;
                        }
                        if(!rv.empty())
                        {
                            p_box *= measure::p_measure(rv);
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
                        if(!rv.empty())
                        {
                            s << rv.min_side_width() * global_config.solver_precision_ratio;
                        }
                        else
                        {
                            s << global_config.solver_precision_ratio;
                        }
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Solver options: " << s.str();
                    }
                    switch(decision_procedure::evaluate(paths, vector<box>{nd, dd, rv}, s.str()))
                    {
                        case decision_procedure::result::SAT:
                        #pragma omp critical
                        {
                            if (p_box.leftBound() > 0)
                            {
                                p_map[nd] = capd::interval(p_map[nd].leftBound() + p_box.leftBound(),
                                                           p_map[nd].rightBound());
                            }
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << std::scientific << p_map[nd];
                        }
                        break;

                        case decision_procedure::result::UNSAT:
                        #pragma omp critical
                        {
                            if (p_box.leftBound() > 0)
                            {
                                p_map[nd]=capd::interval(p_map[nd].leftBound(), p_map[nd].rightBound() - p_box.leftBound());
                            }
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << std::scientific << p_map[nd];
                        }
                        break;

                        case decision_procedure::result::UNDET:
                        #pragma omp critical
                        {
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDET";
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Bisect " << std::scientific << rv;
                            std::vector<box> rv_bisect = box_factory::bisect(rv);
                            rv_stack.insert(rv_stack.end(), rv_bisect.begin(), rv_bisect.end());
                            // updating total partition
                            auto it = find(total_partition.begin(), total_partition.end(), rv);
                            if(it != total_partition.end())
                            {
                                total_partition.erase(it);
                                total_partition.insert(total_partition.end(), rv_bisect.begin(), rv_bisect.end());
                            }
                        }
                        break;
                    }
                }

                if(p_map.find(nd) == p_map.end())
                {
                    CLOG(ERROR, "algorithm") << "The box " << nd << " is not in the map";
                    exit(EXIT_FAILURE);
                }
                capd::interval probability;
                probability = p_map[nd];
                if(capd::intervals::width(probability) <= global_config.precision_prob)
                {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Epsilon is satisfied. Updating resulting probability map with " << nd;
                    p_map.erase(nd);
                    partition_map.erase(nd);
                    res_map[nd] = probability;// * dd_measure;
                }
                // sorting newly obtained boxes
                if(global_config.sort_rv_flag)
                {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Sorting bisected boxes";
                    sort(rv_stack.begin(), rv_stack.end(), measure::compare_boxes_by_p_measure);
                }
                // updating partition map only in case if probability value does not satisfy the probability precision
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "Updating partition map";
                if(partition_map.find(nd) != partition_map.cend())
                {
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
            for(auto it = tmp_map.cbegin(); it != tmp_map.cend(); it++)
            {
                box nd = it->first;
                // checking if the system features nondeterministic parameters
                if(!nd.empty())
                {
                    // bisecting the nondeterministic box
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Bisect " << std::scientific << nd;
                    std::vector<box> tmp_boxes;
                    // checking if the --ignore-nondet flag is up
                    if(global_config.ignore_nondet)
                    {
                        tmp_boxes = box_factory::bisect(nd);
                    }
                    else
                    {
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
                    if(tmp_boxes.size() > 1)
                    {
                        for(box b : tmp_boxes)
                        {
                            p_map.insert(make_pair(b, tmp_prob_value));
                            partition_map.insert(make_pair(b, tmp_rv_partition));
                            res_map.insert(make_pair(b, tmp_prob_value));
                            final_map.insert(make_pair(b, tmp_final_prob_value));
                        }
                    }
                    else
                    {
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
        for(auto it = final_map.begin(); it != final_map.end(); it++)
        {
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
        for(auto it = final_map.begin(); it != final_map.end(); it++)
        {
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

tuple<vector<box>, vector<box>, vector<box>> algorithm::evaluate_psy(map<string, vector<pair<pdrh::node*, pdrh::node*>>> time_series)
{
    // getting the synthesis domain
    box psy_domain = pdrh::get_psy_domain();
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Obtaining domain of synthesized parameters: " << psy_domain;
    // partition of parameter synthesis domain
    vector<box> psy_partition { psy_domain };
    // if flag is enabled the domain is partitioned up to precision_nondet
    /*
    if(global_config.partition_psy)
    {
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Obtaining partition of parameter synthesis domain";
        psy_partition.clear();
        psy_partition = measure::partition(psy_domain, global_config.pre);
    }
    */
    // converting time series to a set of goal boxes
    //std::vector<std::tuple<int, box>> goals = pdrh::series_to_boxes(time_series);
    vector<pdrh::state> goals = pdrh::series_to_goals(time_series);
    // getting parameter synthesis path
    vector<pdrh::mode*> path = pdrh::get_psy_path(time_series);
    // defining the boxes
    vector<box> sat_boxes, undet_boxes, unsat_boxes;
    // iterating through the goals
    //cout << "Before parallel" << endl;
    for(pdrh::state goal : goals)
    {
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Evaluating goal: @" << goal.id << " " << pdrh::node_to_string_prefix(goal.prop);
        // iterating through boxes in psy partition
        while(!psy_partition.empty())
        {
            vector<box> swap_psy_partition;
            #pragma omp parallel for
            for(unsigned long i = 0; i < psy_partition.size(); i++)
            {
                /*
                box b = psy_partition.front();
                psy_partition.erase(psy_partition.cbegin());
                cout << "In parallel section " << b << endl;
                */
                box b = psy_partition.at(i);
                //cout << "In parallel section " << b << endl;
                #pragma omp critical
                {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "psy_box: " << b;
                }
                int res = decision_procedure::evaluate(pdrh::init.front(), goal, path, {b});
                #pragma omp critical
                {
                    switch (res)
                    {
                        case decision_procedure::SAT:
                        {
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                            sat_boxes.push_back(b);
                            //sat_boxes = box_factory::merge(sat_boxes);
                            break;
                        }
                        case decision_procedure::UNSAT:
                        {
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                            unsat_boxes.push_back(b);
                            //unsat_boxes = box_factory::merge(unsat_boxes);
                            break;
                        }
                        case decision_procedure::UNDET:
                        {
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDET";
                            // CHECK FOR BUGS IN BISECT
                            std::vector<box> tmp_vector = box_factory::bisect(b, pdrh::syn_map);
                            if (tmp_vector.size() == 0)
                            {
                                //cout << b << ": UNDET box" <<endl;
                                undet_boxes.push_back(b);
                                //undet_boxes = box_factory::merge(undet_boxes);
                            }
                            else
                            {
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "Bisected";
                                swap_psy_partition.insert(swap_psy_partition.cend(), tmp_vector.cbegin(), tmp_vector.cend());
                            }
                            break;
                        }
                        case decision_procedure::SOLVER_TIMEOUT:
                        {
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "SOLVER_TIMEOUT";
                            break;
                        }
                        case decision_procedure::ERROR:
                        {
                            LOG(ERROR) << "ERROR";
                            break;
                        }
                    }
                }
            }
            psy_partition.clear();
            psy_partition.insert(psy_partition.cend(), swap_psy_partition.cbegin(), swap_psy_partition.cend());
        }
        psy_partition = sat_boxes;
        sat_boxes.clear();
        if(psy_partition.empty())
        {
            break;
        }
    }
    sat_boxes = box_factory::merge(psy_partition);
    undet_boxes = box_factory::merge(undet_boxes);
    unsat_boxes = box_factory::merge(unsat_boxes);
    return std::make_tuple(sat_boxes, undet_boxes, unsat_boxes);
}


capd::interval algorithm::evaluate_pha_chernoff(int min_depth, int max_depth, double acc, double conf, vector<box> nondet_boxes)
{
    const gsl_rng_type * T;
    gsl_rng * r;
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
    #pragma omp parallel for
    for(long int ctr = 0; ctr < sample_size; ctr++)
    {
        std::vector<std::vector<pdrh::mode*>> paths;
        // getting all paths
        for(pdrh::state i : pdrh::init)
        {
            for(pdrh::state g : pdrh::goal)
            {
                for(int j = min_depth; j <= max_depth; j++)
                {
                    std::vector<std::vector<pdrh::mode*>> paths_j = pdrh::get_paths(pdrh::get_mode(i.id), pdrh::get_mode(g.id), j);
                    paths.insert(paths.cend(), paths_j.cbegin(), paths_j.cend());
                }
            }
        }
        // getting a sample
        box b = rnd::get_random_sample(r);
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Random sample: " << b;
        std::vector<box> boxes = { b };
        boxes.insert(boxes.end(), nondet_boxes.begin(), nondet_boxes.end());
        int undet_counter = 0;
        int timeout_counter = 0;
        bool sat_flag = false;
        // evaluating all paths
        for(std::vector<pdrh::mode*> path : paths)
        {
            std::stringstream p_stream;
            for(pdrh::mode* m : path)
            {
                p_stream << m->id << " ";
            }
            // removing trailing whitespace
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Path: " << p_stream.str().substr(0, p_stream.str().find_last_of(" "));
            int res;
            if(global_config.delta_sat)
            {
                res = decision_procedure::evaluate_delta_sat(path, boxes);
            }
            else
            {
                res = decision_procedure::evaluate(path, boxes);
            }
            #pragma omp critical
            {
                if (res == decision_procedure::SAT)
                {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                    sat++;
                    sat_flag = true;
                }
                else if (res == decision_procedure::UNSAT)
                {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                }
                else if (res == decision_procedure::UNDET)
                {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDET";
                    undet_counter++;
                }
                else if (res == decision_procedure::ERROR)
                {
                    CLOG(ERROR, "algorithm") << "Error occured while calling a solver";
                    exit(EXIT_FAILURE);
                }
                else if (res == decision_procedure::SOLVER_TIMEOUT)
                {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "SOLVER_TIMEOUT";
                    timeout_counter++;
                }
            }
            if(sat_flag)
            {
                break;
            }
        }
        // updating unsat counter
        #pragma omp critical
        {
            if ((undet_counter == 0) && (timeout_counter == 0) && (!sat_flag))
            {
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
    return capd::interval(((double) sat / (double) sample_size) - acc, ((double) (sample_size - unsat) / (double) sample_size) + acc);
}

capd::interval algorithm::evaluate_pha_bayesian(int min_depth, int max_depth, double acc, double conf, vector<box> nondet_boxes)
{
    const gsl_rng_type * T;
    gsl_rng * r;
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
    #pragma omp parallel
    while(post_prob < conf)
    {
        std::vector<std::vector<pdrh::mode*>> paths;
        // getting all paths
        for(pdrh::state i : pdrh::init)
        {
            for(pdrh::state g : pdrh::goal)
            {
                for(int j = min_depth; j <= max_depth; j++)
                {
                    std::vector<std::vector<pdrh::mode*>> paths_j = pdrh::get_paths(pdrh::get_mode(i.id), pdrh::get_mode(g.id), j);
                    paths.insert(paths.cend(), paths_j.cbegin(), paths_j.cend());
                }
            }
        }
        // getting a sample
        box b = rnd::get_random_sample(r);
        // increasing the sample size
        #pragma omp critical
        {
            sample_size++;
        }
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Random sample: " << b;
        std::vector<box> boxes = { b };
        boxes.insert(boxes.end(), nondet_boxes.begin(), nondet_boxes.end());
        int undet_counter = 0;
        int timeout_counter = 0;
        bool sat_flag = false;
        // checking solver type
        if(global_config.solver_type == solver::type::DREAL)
        {
            // evaluating all paths
            for(std::vector<pdrh::mode*> path : paths)
            {
                std::stringstream p_stream;
                for(pdrh::mode* m : path)
                {
                    p_stream << m->id << " ";
                }
                // removing trailing whitespace
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "Path: " << p_stream.str().substr(0, p_stream.str().find_last_of(" "));
                int res;
                if(global_config.delta_sat)
                {
                    res = decision_procedure::evaluate_delta_sat(path, boxes);
                }
                else
                {
                    res = decision_procedure::evaluate(path, boxes);
                }
                #pragma omp critical
                {
                    if (res == decision_procedure::SAT)
                    {
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                        sat++;
                        sat_flag = true;
                    }
                    else if (res == decision_procedure::UNSAT)
                    {
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                    }
                    else if (res == decision_procedure::UNDET)
                    {
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDET";
                        undet_counter++;
                    }
                    else if (res == decision_procedure::ERROR)
                    {
                        CLOG(ERROR, "algorithm") << "Error occured while calling a solver";
                        exit(EXIT_FAILURE);
                    }
                    else if (res == decision_procedure::SOLVER_TIMEOUT)
                    {
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "SOLVER_TIMEOUT";
                        timeout_counter++;
                    }
                }
                if(sat_flag)
                {
                    break;
                }
            }
        }
        else if(global_config.solver_type == solver::type::ISAT)
        {
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Evaluating with iSAT:";
            int res = decision_procedure::evaluate_isat(boxes);
            if(res == decision_procedure::SAT)
            {
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                sat++;
                sat_flag = true;
            }
            else if(res == decision_procedure::UNSAT)
            {
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
            }
        }
        else
        {
            stringstream s;
            s << "Unrecognized solver";
            throw runtime_error(s.str().c_str());
        }
        // updating unsat counter
        #pragma omp critical
        {
            if ((undet_counter == 0) && (timeout_counter == 0) && (!sat_flag))
            {
                unsat++;
            }
            post_mean_sat = ((double) sat + alpha) / ((double) sample_size + alpha + beta);
            post_mean_unsat = ((double) sample_size - unsat + alpha) / ((double) sample_size + alpha + beta);
            if(global_config.delta_sat)
            {
                if(post_mean_sat >= acc)
                {
                    post_prob = gsl_cdf_beta_P(post_mean_sat + acc, sat + alpha, sample_size - sat + beta)
                                - gsl_cdf_beta_P(post_mean_sat - acc, sat + alpha, sample_size - sat + beta);
                }
                else
                {
                    post_prob = gsl_cdf_beta_P(post_mean_sat + acc, sat + alpha, sample_size - sat + beta)
                                - gsl_cdf_beta_P(0, sat + alpha, sample_size - sat + beta);
                }
            }
            else
            {
                //cout << "Left: x: " << post_mean_unsat + acc << " alpha: " << sample_size - unsat + alpha << " beta: " << unsat + beta << endl;
                //cout << "Right: x: " << post_mean_sat - acc << " alpha: " << sat + alpha << " beta: " << sample_size - sat + beta << endl;
                //cout << "sample_size: " << sample_size << " sat: " << sat << " beta value: " << beta << endl;
                if(post_mean_sat >= acc)
                {
                    post_prob = gsl_cdf_beta_P(post_mean_unsat + acc, sample_size - unsat + alpha, unsat + beta)
                                - gsl_cdf_beta_P(post_mean_sat - acc, sat + alpha, sample_size - sat + beta);
                }
                else
                {
                    post_prob = gsl_cdf_beta_P(post_mean_unsat + acc, sample_size - unsat + alpha, unsat + beta)
                                - gsl_cdf_beta_P(0, sat + alpha, sample_size - sat + beta);
                }
            }
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "CI: " << capd::interval(post_mean_sat - acc, post_mean_unsat + acc);
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "P(SAT) mean: " << post_mean_sat;
            if(!global_config.delta_sat)
            {
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "P(UNSAT) mean: " << post_mean_unsat;
            }
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Random sample size: " << sample_size;
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "P prob: " << post_prob;
        }
    }
    gsl_rng_free(r);
    // displaying sample size if enabled
    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Random sample size: " << sample_size;
    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Bayesian estimations algorithm finished";
    if(global_config.delta_sat)
    {
        return capd::interval(post_mean_sat - acc, post_mean_sat + acc);
    }
    else
    {
        return capd::interval(post_mean_sat - acc, post_mean_unsat + acc);
    }
}

capd::interval algorithm::evaluate_pha_chernoff(int min_depth, int max_depth, double acc, double conf)
{
    return evaluate_pha_chernoff(min_depth, max_depth, acc, conf, vector<box>{});
}

capd::interval algorithm::evaluate_pha_bayesian(int min_depth, int max_depth, double acc, double conf)
{
    return evaluate_pha_bayesian(min_depth, max_depth, acc, conf, vector<box>{});
}

long int algorithm::get_cernoff_bound(double acc, double conf)
{
    if((acc <= 0) || (conf < 0) || (conf >= 1))
    {
        CLOG(ERROR, "algorithm") << "accuracy must be descending than 0 and confidence must be inside [0, 1) interval";
    }
    return (long int) std::ceil((1/(2 * acc * acc)) * std::log(2/(1 - conf)));
}

pair<box, capd::interval> algorithm::evaluate_npha_sobol(int min_depth, int max_depth, int size)
{
    gsl_qrng * q = gsl_qrng_alloc(gsl_qrng_sobol, pdrh::par_map.size());

    //initializing probability value
    pair<box, capd::interval> res;
    if(global_config.max_prob)
    {
        res = make_pair(box(), capd::interval(0.0));
    }
    else
    {
        res = make_pair(box(), capd::interval(1.0));
    }
    box domain = pdrh::get_nondet_domain();
    vector<pair<box, capd::interval>> samples;
    while(domain.max_side_width() > global_config.sobol_term_arg)
    {
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Explored space: " << domain << " | " << domain.max_side_width();
        for (int i = 0; i < size; i++)
        {
            box b = rnd::get_sobol_sample(q, domain);
            CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Quasi-random sample: " << b;
            capd::interval probability;
            if (global_config.bayesian_flag)
            {
                probability = evaluate_pha_bayesian(min_depth, max_depth, global_config.bayesian_acc,
                                                    global_config.bayesian_conf, vector<box>{b});
            }
            else if (global_config.chernoff_flag)
            {
                probability = evaluate_pha_chernoff(min_depth, max_depth, global_config.chernoff_acc,
                                                    global_config.chernoff_conf, vector<box>{b});
            }
            else
            {
                CLOG(ERROR, "algorithm") << "Unknown setting";
                exit(EXIT_FAILURE);
            }
            // fixing probability value
            if (probability.leftBound() < 0)
            {
                probability.setLeftBound(0);
            }
            if (probability.rightBound() > 1)
            {
                probability.setRightBound(1);
            }
            CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Probability: " << probability << endl;
            samples.push_back(make_pair(b, probability));
        }
        if (global_config.max_prob)
        {
            sort(samples.begin(), samples.end(), measure::compare_pairs::descending);
        }
        else
        {
            sort(samples.begin(), samples.end(), measure::compare_pairs::ascending);
        }
        vector<pair<box, capd::interval>> elite;
        copy_n(samples.begin(), ceil(samples.size() * global_config.elite_ratio), back_inserter(elite));
        vector<box> elite_boxes;
        for (pair<box, capd::interval> p : elite)
        {
            elite_boxes.push_back(p.first);
        }
        res = samples.front();
        samples.clear();
        domain = box_factory::get_cover(elite_boxes);
    }
    gsl_qrng_free (q);
    return res;
}

pair<box, capd::interval> algorithm::evaluate_npha_cross_entropy_normal(int min_depth, int max_depth, int size)
{
    // random number generator for cross entropy
    const gsl_rng_type * T;
    gsl_rng * r;
    gsl_rng_env_setup();
    T = gsl_rng_default;
    // creating random generator
    r = gsl_rng_alloc(T);
    // setting the seed
    gsl_rng_set(r, std::chrono::system_clock::now().time_since_epoch() / std::chrono::milliseconds(1));
    box domain = pdrh::get_nondet_domain();
    //initializing probability value
    pair<box, capd::interval> res(domain, capd::interval(0.0));
    if(global_config.min_prob)
    {
        res = make_pair(domain, capd::interval(1.0));
    }
    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Domain of nondeterministic parameters: " << domain;
    box mean = domain.get_mean();
    box sigma = domain.get_stddev();
    box var = sigma*sigma;
    vector<pair<box, capd::interval>> samples;
    //#pragma omp parallel
    while(var.max_coordinate_value() > global_config.cross_entropy_term_arg)
    {
        var = sigma*sigma;
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Mean: " << mean;
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Standard deviation: " << sigma;
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Variance: " << var;
        unsigned long new_size = (unsigned long)ceil(size / measure::get_sample_prob(domain, mean, sigma).rightBound());
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Sample size: " << new_size;
        int outliers = 0;
        //#pragma omp parallel for
        for(int i = 0; i < new_size; i++)
        {
            box b = rnd::get_normal_random_sample(r, mean, sigma);
            CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Quasi-random sample: " << b;
            capd::interval probability;
            if(domain.contains(b))
            {
                CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "The sample is inside the domain";
                if(global_config.bayesian_flag)
                {
                    probability = evaluate_pha_bayesian(min_depth, max_depth, global_config.bayesian_acc, global_config.bayesian_conf, vector<box>{ b });
                }
                else if(global_config.chernoff_flag)
                {
                    probability = evaluate_pha_chernoff(min_depth, max_depth, global_config.chernoff_acc, global_config.chernoff_conf, vector<box>{ b });
                }
                else
                {
                    CLOG(ERROR, "algorithm") << "Unknown setting";
                    exit(EXIT_FAILURE);
                }
                // fixing probability value
                if(probability.leftBound() < 0)
                {
                    probability.setLeftBound(0);
                }
                if(probability.rightBound() > 1)
                {
                    probability.setRightBound(1);
                }
            }
            else
            {
                CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "The sample is outside the domain";
                outliers++;
                if(global_config.max_prob)
                {
                    probability = capd::interval(-numeric_limits<double>::infinity());
                }
                else
                {
                    probability = capd::interval(numeric_limits<double>::infinity());
                }
            }
            CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Probability: " << probability << endl;
            samples.push_back(make_pair(b, probability));
        }
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Number of outliers: " << outliers << endl;
        if(global_config.max_prob)
        {
            sort(samples.begin(), samples.end(), measure::compare_pairs::descending);
        }
        else
        {
            sort(samples.begin(), samples.end(), measure::compare_pairs::ascending);
        }
        vector<pair<box, capd::interval>> elite;
        copy_n(samples.begin(), ceil(samples.size() * global_config.elite_ratio), back_inserter(elite));
        // getting elite boxes
        vector<box> elite_boxes;
        for(pair<box, capd::interval> p : elite)
        {
            elite_boxes.push_back(p.first);
        }
        // updating resulting probability
        if(global_config.min_prob)
        {
            if(samples.front().second.mid().leftBound() < res.second.mid().leftBound())
            {
                res = samples.front();
            }
        }
        else
        {
            if(samples.front().second.mid().leftBound() > res.second.mid().leftBound())
            {
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

pair<box, capd::interval> algorithm::evaluate_npha_cross_entropy_beta(int min_depth, int max_depth, int size)
{
    // random number generator for cross entropy
    const gsl_rng_type * T;
    gsl_rng * r;
    gsl_rng_env_setup();
    T = gsl_rng_default;
    // creating random generator
    r = gsl_rng_alloc(T);
    // setting the seed
    gsl_rng_set(r, std::chrono::system_clock::now().time_since_epoch() / std::chrono::milliseconds(1));
    //initializing probability value
    pair<box, capd::interval> res;
    box domain = pdrh::get_nondet_domain();
    CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Domain of nondeterministic parameters: " << domain;
    map<string, capd::interval> one_map, two_map, d_map, half_map;
    d_map = domain.get_map();
    for(auto it = d_map.cbegin(); it != d_map.cend(); it++)
    {
        one_map.insert(make_pair(it->first, capd::interval(1.0)));
        two_map.insert(make_pair(it->first, capd::interval(2.0)));
    }
    box alpha(one_map), beta(one_map), one(one_map), two(two_map);
    //box mode = box_factory::map_box(two, domain);
    //box old_mode = mode;
    box var = (alpha*beta)/((alpha+beta)*(alpha+beta)*(alpha+beta+one));
    //int term_counter = 0;
    vector<pair<box, capd::interval>> samples;
    //#pragma omp parallel
    while(var.max_coordinate_value() > global_config.cross_entropy_term_arg)
    {
        var = (alpha*beta)/((alpha+beta)*(alpha+beta)*(alpha+beta+one));
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Alpha: " << alpha;
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Beta: " << beta;
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Variance: " << var;
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Sample size: " << size;
        //#pragma omp parallel for
        for(int i = 0; i < size; i++)
        {
            box b = rnd::get_beta_random_sample(r, alpha, beta, domain);
            CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Quasi-random sample: " << b;
            capd::interval probability;
            CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "The sample is inside the domain";
            if(global_config.bayesian_flag)
            {
                probability = evaluate_pha_bayesian(min_depth, max_depth, global_config.bayesian_acc, global_config.bayesian_conf, vector<box>{ b });
            }
            else if(global_config.chernoff_flag)
            {
                probability = evaluate_pha_chernoff(min_depth, max_depth, global_config.chernoff_acc, global_config.chernoff_conf, vector<box>{ b });
            }
            else
            {
                CLOG(ERROR, "algorithm") << "Unknown setting";
                exit(EXIT_FAILURE);
            }
            // fixing probability value
            if(probability.leftBound() < 0)
            {
                probability.setLeftBound(0);
            }
            if(probability.rightBound() > 1)
            {
                probability.setRightBound(1);
            }
            CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Probability: " << probability << endl;
            samples.push_back(make_pair(b, probability));
        }
        if(global_config.max_prob)
        {
            sort(samples.begin(), samples.end(), measure::compare_pairs::descending);
        }
        else
        {
            sort(samples.begin(), samples.end(), measure::compare_pairs::ascending);
        }
        vector<pair<box, capd::interval>> elite;
        copy_n(samples.begin(), ceil(samples.size() * global_config.elite_ratio), back_inserter(elite));
        vector<box> elite_boxes;
        for(pair<box, capd::interval> p : elite)
        {
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































