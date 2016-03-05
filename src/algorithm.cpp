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

capd::interval algorithm::evaluate_pha(int depth)
{
    // getting domain of continuous random variables
    box rv_domain = measure::bounds::get_rv_domain();
    // getting partition of domain of continuous random variables
    std::vector<box> rv_partition;
    //rv_partition = measure::get_rv_partition();
    rv_partition.push_back(rv_domain);
    // ADD A FUNCTION WHICH FIXES ALL THE BOUNDS
    // getting partition of domain of discrete random variables
    std::vector<box> dd_partition = measure::get_dd_partition();
    // checking if there are multiple initial and goal states
    if((pdrh::init.size() > 1) || (pdrh::goal.size() > 1))
    {
        CLOG(WARNING, "algorithm") << "Multiple initial or goal states are not supported";
    }
    capd::interval probability(1 - measure::p_measure(measure::bounds::get_rv_domain()).leftBound(), 1);
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "P = " << probability;
    std::vector<std::vector<pdrh::mode*>> paths = pdrh::get_paths(pdrh::get_mode(pdrh::init.front().id), pdrh::get_mode(pdrh::goal.front().id), depth);
    for(std::vector<pdrh::mode*> path : paths)
    {
        std::stringstream p_stream;
        for(pdrh::mode* m : path)
        {
            p_stream << m->id << " ";
        }
        // removing trailing whitespace
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Path: " << p_stream.str().substr(0, p_stream.str().find_last_of(" "));
        for(box dd : dd_partition)
        {
            std::vector<box> rv_stack;
            for(box rv : rv_partition)
            {
                // calculating probability measure of the box
                // initally p_box = [1.0, 1.0]
                capd::interval p_box(1);
                if(!dd.empty())
                {
                    p_box *= measure::p_measure(dd);
                }
                if(!rv.empty())
                {
                    p_box *= measure::p_measure(rv);
                }
                //LOG(INFO) << "dd_box: " << dd;
                //LOG(INFO) << "rv_box: " << rv;
                //LOG(INFO) << "p_box = " << p_box;
                // evaluating boxes
                std::vector<box> boxes;
                boxes.push_back(dd);
                boxes.push_back(rv);
                //int res = decision_procedure::evaluate(pdrh::init.front(), pdrh::goal.front(), path, boxes);
                int res = decision_procedure::evaluate(path, boxes);
                if(res == decision_procedure::SAT)
                {
                    if(p_box.leftBound() > 0)
                    {
                        probability = capd::interval(probability.leftBound() + p_box.leftBound(), probability.rightBound());
                    }
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT; P = " << std::scientific << probability;
                    if(capd::intervals::width(probability) <= global_config.precision_prob)
                    {
                        return probability;
                    }
                }
                else if(res == decision_procedure::UNSAT)
                {
                    if(p_box.leftBound() > 0)
                    {
                        probability = capd::interval(probability.leftBound(), probability.rightBound() - p_box.leftBound());
                    }
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT; P = " << std::scientific << probability;
                    if(capd::intervals::width(probability) <= global_config.precision_prob)
                    {
                        return probability;
                    }
                }
                else if(res == decision_procedure::UNDET)
                {
                    std::vector<box> rv_bisect = box_factory::bisect(rv);
                    rv_stack.insert(rv_stack.end(), rv_bisect.begin(), rv_bisect.end());
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDEC; P = " << std::scientific << probability;
                }
                else if(res == decision_procedure::ERROR)
                {
                    CLOG(ERROR, "algorithm") << "Error occurred while calling the solver";
                    return EXIT_FAILURE;
                }
                else if(res == decision_procedure::SOLVER_TIMEOUT)
                {
                    std::vector<box> rv_bisect = box_factory::bisect(rv);
                    rv_stack.insert(rv_stack.end(), rv_bisect.begin(), rv_bisect.end());
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "SOLVER_TIMEOUT; P = " << std::scientific << probability;
                }
            }
            // HERE WE NEED TO COME BACK TO THE RV LOOP
            rv_partition = rv_stack;
            rv_stack.clear();
        }
    }
    //return probability;
}