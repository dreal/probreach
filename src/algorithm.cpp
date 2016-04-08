//
// Created by fedor on 03/03/16.
//

#include <gsl/gsl_rng.h>
#include "algorithm.h"
#include "easylogging++.h"
#include "pdrh_config.h"
#include "measure.h"
#include "box_factory.h"
#include<chrono>
#include <iomanip>
#include "rnd.h"

decision_procedure::result algorithm::evaluate_ha(int depth)
{
    int undet_counter = 0;
    for(pdrh::state i : pdrh::init)
    {
        for(pdrh::state g : pdrh::goal)
        {
            std::vector<std::vector<pdrh::mode*>> paths = pdrh::get_paths(pdrh::get_mode(i.id), pdrh::get_mode(g.id), depth);
            for(std::vector<pdrh::mode*> path : paths)
            {
                std::stringstream p_stream;
                for(pdrh::mode* m : path)
                {
                    p_stream << m->id << " ";
                }
                // removing trailing whitespace
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "Path: " << p_stream.str().substr(0, p_stream.str().find_last_of(" "));
                std::vector<box> boxes;
                int res = decision_procedure::evaluate(i, g, path, boxes);
                if(res == decision_procedure::SAT)
                {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                    return decision_procedure::SAT;
                }
                else if(res == decision_procedure::UNSAT)
                {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                }
                else if(res == decision_procedure::UNDET)
                {
                    undet_counter++;
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDET";
                }
                else if(res == decision_procedure::ERROR)
                {
                    return decision_procedure::ERROR;
                }
                else if(res == decision_procedure::SOLVER_TIMEOUT)
                {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "SOLVER_TIMEUT";
                }
            }
        }
    }
    // checking if either of the paths was UNDET
    if(undet_counter > 0)
    {
        return decision_procedure::UNDET;
    }
    return decision_procedure::UNSAT;
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
    std::vector<box> rv_partition = measure::get_rv_partition();
    // getting domain of continuous random variables
    box rv_domain = measure::bounds::get_rv_domain();
    // here we start with entire domain instead of partition
    if(!global_config.partition_prob)
    {
        rv_partition.clear();
        rv_partition.push_back(rv_domain);
    }
    // getting partition of domain of discrete random variables
    std::vector<box> dd_partition = measure::get_dd_partition();
    // checking if there are multiple initial and goal states
    if((pdrh::init.size() > 1) || (pdrh::goal.size() > 1))
    {
        CLOG(WARNING, "algorithm") << "Multiple initial or goal states are not supported";
    }
    capd::interval probability(0,1);
    // checking if there are any continuous random variables
    if(pdrh::rv_map.size() > 0)
    {
        probability = capd::interval(0, 2 - measure::p_measure(rv_domain).leftBound());
    }
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << std::scientific << probability;
    // generating all paths of lengths [min_depth, max_depth]
    std::vector<std::vector<pdrh::mode*>> paths;
    for(int i = min_depth; i <= max_depth; i++)
    {
        std::vector<std::vector<pdrh::mode*>> paths_i = pdrh::get_paths(pdrh::get_mode(pdrh::init.front().id), pdrh::get_mode(pdrh::goal.front().id), i);
        paths.insert(paths.cend(), paths_i.cbegin(), paths_i.cend());
    }
    // evaluating boxes
    for(box dd : dd_partition)
    {
        std::vector<box> rv_stack;
        while(capd::intervals::width(probability) > global_config.precision_prob)
        {
            for(box rv : rv_partition)
            {
                // calculating probability measure of the box
                // initially p_box = [1.0, 1.0]
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "====================" << dd;
                capd::interval p_box(1);
                if (!dd.empty())
                {
                    p_box *= measure::p_measure(dd);
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "dd_box: " << dd;
                }
                if (!rv.empty())
                {
                    p_box *= measure::p_measure(rv);
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "rv_box: " << rv;
                }
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "p_box: " << p_box;
                // evaluating boxes
                std::vector<box> boxes;
                boxes.push_back(dd);
                boxes.push_back(rv);
                // undetermined answers counter
                int undet_counter = 0;
                // solver timeout counter
                int timeout_counter = 0;
                // unsat counter
                int unsat_counter = 0;
                // sat flag
                bool sat_flag = false;
                // evaluating all paths for all dd and rv
                for (std::vector<pdrh::mode *> path : paths)
                {
                    std::stringstream p_stream;
                    for (pdrh::mode *m : path)
                    {
                        p_stream << m->id << " ";
                    }
                    // removing trailing whitespace
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Path: " << p_stream.str().substr(0, p_stream.str().find_last_of(" "));
                    // changing solver precision
                    std::string solver_opt = global_config.solver_opt;
                    std::stringstream s;
                    s << solver_opt << " --precision " << measure::volume(rv).leftBound() * global_config.solver_precision_ratio;
                    global_config.solver_opt = s.str();
                    int res = decision_procedure::evaluate(path, boxes);
                    // setting old precision
                    global_config.solver_opt = solver_opt;

                    if(res == decision_procedure::SAT)
                    {
                        if(p_box.leftBound() > 0)
                        {
                            probability = capd::interval(probability.leftBound() + p_box.leftBound(), probability.rightBound());
                        }
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << std::scientific << probability;
                        if(capd::intervals::width(probability) <= global_config.precision_prob)
                        {
                            return probability;
                        }
                        sat_flag = true;
                        break;
                    }
                    else if(res == decision_procedure::UNSAT)
                    {
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                        unsat_counter++;
                    }
                    else if(res == decision_procedure::UNDET)
                    {
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDEC";
                        undet_counter++;
                    }
                    else if(res == decision_procedure::ERROR)
                    {
                        CLOG(ERROR, "algorithm") << "Error occurred while calling the solver";
                        return EXIT_FAILURE;
                    }
                    else if(res == decision_procedure::SOLVER_TIMEOUT)
                    {
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "SOLVER_TIMEOUT";
                        timeout_counter++;
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
                        if (capd::intervals::width(probability) <= global_config.precision_prob)
                        {
                            return probability;
                        }
                    }
                }
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
    }
    return probability;
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
        nd_partition = measure::partition(nd_domain, global_config.precision_nondet);
    }
    // getting partition of domain of continuous random variables
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Obtaining partition of domain of continuous random parameters";
    std::vector<box> rv_partition = measure::get_rv_partition();
    // getting domain of continuous random variables
    box rv_domain = measure::bounds::get_rv_domain();
    // here we start with entire domain instead of partition
    if(!global_config.partition_prob)
    {
        rv_partition.clear();
        rv_partition.push_back(rv_domain);
    }
    // getting partition of domain of discrete random variables
    std::vector<box> dd_partition = measure::get_dd_partition();
    // checking if there are multiple initial and goal states
    if((pdrh::init.size() > 1) || (pdrh::goal.size() > 1))
    {
        CLOG(WARNING, "algorithm") << "Multiple initial or goal states are not supported";
    }
    // generating all paths of lengths [min_depth, max_depth]
    std::vector<std::vector<pdrh::mode*>> paths;
    for(int i = min_depth; i <= max_depth; i++)
    {
        std::vector<std::vector<pdrh::mode*>> paths_i = pdrh::get_paths(pdrh::get_mode(pdrh::init.front().id), pdrh::get_mode(pdrh::goal.front().id), i);
        paths.insert(paths.cend(), paths_i.cbegin(), paths_i.cend());
    }
    // initializing probability map
    std::map<box, capd::interval> p_map;
    for(box nd : nd_partition)
    {
        p_map.insert(std::make_pair(nd, capd::interval(0, 2 - measure::p_measure(rv_domain).leftBound())));
    }
    // initializing partition map
    std::map<box, std::vector<box>> partition_map;
    for(box nd : nd_partition)
    {
        partition_map.insert(std::make_pair(nd, rv_partition));
    }
    std::map<box, capd::interval> res_map;
    // algorithm
    while(p_map.size() > 0)
    {
        // updating the nd_partition
        nd_partition.clear();
        for(auto it = p_map.cbegin(); it != p_map.cend(); it++)
        {
            nd_partition.push_back(it->first);
        }
        // iterating through the boxes
        for(box nd : nd_partition)
        {
            for(box dd : dd_partition)
            {
                rv_partition = partition_map[nd];
                std::vector<box> rv_stack;
                for (box rv : rv_partition)
                {
                    // calculating probability measure of the box rv
                    // initally p_box = [1.0, 1.0]
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "====================";
                    capd::interval p_box(1);
                    if(!nd.empty())
                    {
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "nd_box: " << nd;
                    }
                    if(!dd.empty())
                    {
                        p_box *= measure::p_measure(dd);
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "dd_box: " << dd;
                    }
                    if(!rv.empty())
                    {
                        p_box *= measure::p_measure(rv);
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "rv_box: " << rv;
                    }
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "p_box: " << p_box;
                    // setting the box vector to evaluate
                    std::vector<box> boxes;
                    boxes.push_back(nd);
                    boxes.push_back(dd);
                    boxes.push_back(rv);
                    // undetermined answers counter
                    int undet_counter = 0;
                    // solver timeout counter
                    int timeout_counter = 0;
                    // unsat counter
                    int unsat_counter = 0;
                    // sat flag
                    bool sat_flag = false;
                    // evaluating all paths for all dd and rv
                    for (std::vector<pdrh::mode *> path : paths)
                    {
                        std::stringstream p_stream;
                        for (pdrh::mode *m : path)
                        {
                            p_stream << m->id << " ";
                        }
                        // removing trailing whitespace
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Path: " << p_stream.str().substr(0, p_stream.str().find_last_of(" "));
                        // changing solver precision
                        std::string solver_opt = global_config.solver_opt;
                        std::stringstream s;
                        s << solver_opt << " --precision " << measure::volume(rv).leftBound() * global_config.solver_precision_ratio;
                        global_config.solver_opt = s.str();
                        int res = decision_procedure::evaluate(path, boxes);
                        // setting old precision
                        global_config.solver_opt = solver_opt;

                        if(res == decision_procedure::SAT)
                        {
                            capd::interval probability;
                            if(p_box.leftBound() > 0)
                            {
                                probability = capd::interval(p_map[nd].leftBound() + p_box.leftBound(), p_map[nd].rightBound());
                            }
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << std::scientific << probability;
                            if(capd::intervals::width(probability) <= global_config.precision_prob)
                            {
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "Updating resulting probability map";
                                p_map.erase(nd);
                                partition_map.erase(nd);
                                res_map.insert(std::make_pair(nd, probability));
                            }
                            else
                            {
                                p_map[nd] = probability;
                            }
                            sat_flag = true;
                            break;
                        }
                        else if(res == decision_procedure::UNSAT)
                        {
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                            unsat_counter++;
                        }
                        else if(res == decision_procedure::UNDET)
                        {
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDEC";
                            undet_counter++;
                        }
                        else if(res == decision_procedure::ERROR)
                        {
                            CLOG(ERROR, "algorithm") << "Error occurred while calling the solver";
                            //return ;
                        }
                        else if(res == decision_procedure::SOLVER_TIMEOUT)
                        {
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "SOLVER_TIMEOUT";
                            timeout_counter++;
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
                            capd::interval probability;
                            if (p_box.rightBound() > 0)
                            {
                                 probability = capd::interval(p_map[nd].leftBound(), p_map[nd].rightBound() - p_box.leftBound());
                            }
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << std::scientific << probability;
                            if(capd::intervals::width(probability) <= global_config.precision_prob)
                            {
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "Updating resulting probability map";
                                p_map.erase(nd);
                                partition_map.erase(nd);
                                res_map.insert(std::make_pair(nd, probability));
                            }
                            else
                            {
                                p_map[nd] = probability;
                            }
                        }
                    }
                }
                // updating partition map only in case if probability value does not satisfy the probability precision
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "Updating partition map";
                if(partition_map.find(nd) != partition_map.cend())
                {
                    partition_map[nd] = rv_stack;
                }
                std::cout << "p_map:" << std::endl;
                for(auto it = p_map.cbegin(); it != p_map.cend(); it++)
                {
                    std::cout << std::scientific << it->first << " | " << it->second << std::endl;
                }
            }
        }
        // updating probability and partition maps
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Updating probability map";
        std::map<box, capd::interval> tmp_map = p_map;
        for(auto it = tmp_map.cbegin(); it != tmp_map.cend(); it++)
        {
            // bisecting the nondeterministic box
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Bisect " << std::scientific << it->first;
            std::vector<box> tmp_boxes = box_factory::bisect(it->first);
            capd::interval tmp_prob_value = p_map[it->first];
            std::vector<box> tmp_rv_partition = partition_map[it->first];
            // removing probability and partition for the bisected box
            p_map.erase(it->first);
            partition_map.erase(it->first);
            // updating probability and partition maps
            for(box b : tmp_boxes)
            {
                p_map.insert(std::make_pair(b, tmp_prob_value));
                partition_map.insert(std::make_pair(b, tmp_rv_partition));
            }
            /*
            std::cout << "p_map after:" << std::endl;
            for(auto it2 = p_map.cbegin(); it2 != p_map.cend(); it2++)
            {
                std::cout << std::scientific << it2->first << " | " << it2->second << std::endl;
            }
            */
        }
        /*
        std::cout << "p_map:" << std::endl;
        for(auto it = p_map.cbegin(); it != p_map.cend(); it++)
        {
            std::cout << std::scientific << it->first << " | " << it->second << std::endl;
        }
        */
    }
    return res_map;
}

std::tuple<std::vector<box>, std::vector<box>, std::vector<box>> algorithm::evaluate_psy(std::map<std::string, std::vector<capd::interval>> time_series)
{
    // getting the synthesis domain
    box psy_domain = pdrh::get_psy_domain();
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Obtaining domain of synthesized parameters: " << psy_domain;
    // partition of parameter synthesis domain
    std::vector<box> psy_partition { psy_domain };
    // converting time series to a set of goal boxes
    std::vector<std::tuple<int, box>> goals = pdrh::series_to_boxes(time_series);
    // getting parameter synthesis path
    std::vector<pdrh::mode*> path = pdrh::get_psy_path(time_series);
    // defining the boxes
    std::vector<box> sat_boxes, undet_boxes, unsat_boxes;
    // iterating through the goals
    for(std::tuple<int, box> goal : goals)
    {
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Evaluating goal: @" << std::get<0>(goal) << " " << std::get<1>(goal);
        // iterating through boxes in psy partition
        while(!psy_partition.empty())
        {
            box b = psy_partition.front();
            psy_partition.erase(psy_partition.cbegin());
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "psy_box: " << b;
            switch(decision_procedure::synthesize(pdrh::init.front(), path, b, std::get<0>(goal), std::get<1>(goal)))
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
                    std::vector<box> tmp_vector = box_factory::bisect(b, pdrh::syn_map);
                    if(tmp_vector.size() == 1)
                    {
                        undet_boxes.push_back(b);
                        //undet_boxes = box_factory::merge(undet_boxes);
                    }
                    else
                    {
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Bisected";
                        psy_partition.insert(psy_partition.cend(), tmp_vector.cbegin(), tmp_vector.cend());
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
        // putting the boxes satisfying the current goal back to the psy partition
        psy_partition = box_factory::merge(sat_boxes);
        undet_boxes = box_factory::merge(undet_boxes);
        unsat_boxes = box_factory::merge(unsat_boxes);
        //psy_partition = sat_boxes;
        sat_boxes.clear();
    }
    return std::make_tuple(psy_partition, undet_boxes, unsat_boxes);
}

capd::interval algorithm::evaluate_pha_chernoff(int min_depth, int max_depth, double acc, double conf)
{
    const gsl_rng_type * T;
    gsl_rng * r;
    gsl_rng_env_setup();
    T = gsl_rng_default;
    // creating random generator
    r = gsl_rng_alloc(T);
    // setting the seed
    gsl_rng_set(r, std::chrono::system_clock::now().time_since_epoch() /
                   std::chrono::milliseconds(1));
    // getting sample size with recalculated confidence
    long int sample_size = algorithm::get_cernoff_bound(acc, std::sqrt(conf));
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Sample size: " << sample_size;
    long int sat = 0;
    long int unsat = 0;
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
        box b = rnd::get_sample(r);
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Sample: " << b;
        std::vector<box> boxes = { b };
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
            int res = decision_procedure::evaluate(path, boxes);
            if(res == decision_procedure::SAT)
            {
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                sat++;
                sat_flag = true;
                break;
            }
            else if(res == decision_procedure::UNSAT)
            {
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
            }
            else if(res == decision_procedure::UNDET)
            {
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDET";
                undet_counter++;
            }
            else if(res == decision_procedure::ERROR)
            {
                CLOG(ERROR, "algorithm") << "Error occured while calling a solver";
                exit(EXIT_FAILURE);
            }
            else if(res == decision_procedure::SOLVER_TIMEOUT)
            {
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "SOLVER_TIMEOUT";
                timeout_counter++;
            }
        }
        // updating unsat counter
        if((undet_counter == 0) && (timeout_counter == 0) && (!sat_flag))
        {
            unsat++;
        }
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Progress: " << (double) ctr / (double) sample_size;
    }
    gsl_rng_free(r);
    return capd::interval(((double) sat / (double) sample_size) - acc / 2, ((double) (sample_size - unsat) / (double) sample_size) + acc / 2);
}

long int algorithm::get_cernoff_bound(double acc, double conf)
{
    if((acc <= 0) || (conf < 0) || (conf >= 1))
    {
        CLOG(ERROR, "algorithm") << "accuracy must be greater than 0 and confidence must be inside [0, 1) interval";
    }
    return (long int) std::ceil((1/(2 * acc * acc)) * std::log(1/(1 - conf)));
}





