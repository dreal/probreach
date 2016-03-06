//
// Created by fedor on 03/03/16.
//

#include "algorithm.h"
#include "easylogging++.h"
#include "pdrh_config.h"
#include "measure.h"
#include "box_factory.h"

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
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Obtaining partition of continuous random variables domain";
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
    capd::interval probability(0, 2 - measure::p_measure(measure::bounds::get_rv_domain()).leftBound());
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
                // initally p_box = [1.0, 1.0]
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
        }
    }
    return probability;
}