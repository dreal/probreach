//
// Created by fedor on 03/03/16.
//

#include <gsl/gsl_rng.h>
#include <gsl/gsl_qrng.h>
#include <gsl/gsl_cdf.h>
#include "algorithm.h"
#include "easylogging++.h"
#include "pdrh_config.h"
#include "measure.h"
#include "box_factory.h"
#include <chrono>
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
                int res;
                // checking here if the delta-sat flag is enabled
                if(global_config.delta_sat)
                {
                    res = decision_procedure::evaluate_delta_sat(path, boxes);
                }
                else
                {
                    res = decision_procedure::evaluate(path, boxes);
                }
                // checking the returned value
                if(res == decision_procedure::SAT)
                {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                    return decision_procedure::SAT;
                }
                else if(res == decision_procedure::UNSAT)
                {
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                }
                // never happens when --delta-sat is enabled
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
    // never is returned when --delta-sat is enabled
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
            //#pragma omp parallel for
            //for(box rv : rv_partition)
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
                    //#pragma omp critical
                    //{
                        switch (res)
                        {
                            case decision_procedure::SAT:
                                if (p_box.leftBound() > 0)
                                {
                                    probability = capd::interval(probability.leftBound() + p_box.leftBound(),
                                                                 probability.rightBound());
                                }
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                                CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << std::scientific <<
                                                                                  probability;
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
                    //}
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
        //nd_partition = measure::partition(nd_domain, global_config.precision_nondet);
        nd_partition = box_factory::partition(nd_domain, global_config.precision_nondet);
        /*
        for(box nd : nd_partition)
        {
            cout << nd << endl;
        }
        */
    }
    //exit(EXIT_SUCCESS);
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
                        p_box *= measure::p_dd_measure(dd);
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
                /*
                std::cout << "p_map:" << std::endl;
                for(auto it = p_map.cbegin(); it != p_map.cend(); it++)
                {
                    std::cout << std::scientific << it->first << " | " << it->second << std::endl;
                }
                */
            }
        }
        // updating probability and partition maps
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Updating probability map";
        std::map<box, capd::interval> tmp_map = p_map;
        for(auto it = tmp_map.cbegin(); it != tmp_map.cend(); it++)
        {
            // bisecting the nondeterministic box
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Bisect " << std::scientific << it->first;
            std::vector<box> tmp_boxes = box_factory::partition(it->first, global_config.precision_nondet);
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
    for(pdrh::state goal : goals)
    {
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Evaluating goal: @" << goal.id << " " << pdrh::node_to_string_prefix(goal.prop);
        // iterating through boxes in psy partition
        while(!psy_partition.empty())
        {
            box b = psy_partition.front();
            psy_partition.erase(psy_partition.cbegin());
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "psy_box: " << b;
            switch(decision_procedure::evaluate(pdrh::init.front(), goal, path, {b}))
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
                    if(tmp_vector.size() == 0)
                    {
                        //cout << b << ": UNDET box" <<endl;
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
        //psy_partition = box_factory::merge(sat_boxes);
        //undet_boxes = box_factory::merge(undet_boxes);
        //unsat_boxes = box_factory::merge(unsat_boxes);
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

pair<box, capd::interval> algorithm::evaluate_npha_cross_entropy(int min_depth, int max_depth, int size)
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
    box mean = domain.get_mean();
    box sigma = domain.get_stddev();
    box new_sigma = sigma;
    vector<pair<box, capd::interval>> samples;
    //#pragma omp parallel
    while(new_sigma.max_coordinate_value() > global_config.cross_entropy_term_arg)
    {
        new_sigma = sigma;
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Mean: " << mean;
        CLOG_IF(global_config.verbose_result, INFO, "algorithm") << "Standard deviation: " << sigma;
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
        vector<box> elite_boxes;
        for(pair<box, capd::interval> p : elite)
        {
            elite_boxes.push_back(p.first);
        }
        res = samples.front();
        samples.clear();
        mean = box_factory::get_mean(elite_boxes);
        sigma = box_factory::get_stddev(elite_boxes);
    }
    gsl_rng_free(r);
    return res;
}

