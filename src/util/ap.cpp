//
// Created by fedor on 22/09/17.
//

#include "ap.h"
#include "pdrh_config.h"
#include "box_factory.h"
#include <capd/capdlib.h>
#include <capd/intervals/lib.h>
#include <logging/easylogging++.h>
#include <gsl/gsl_randist.h>
#include <chrono>
#include <solver/dreal_wrapper.h>
#include "decision_procedure.h"
#include "pdrh2box.h"

using namespace pdrh;

capd::interval ap::get_sample_rate(pdrh::node* n)
{
    auto *node_copy = new pdrh::node;
    pdrh::copy_tree(node_copy, n);
    auto *time_node = new pdrh::node;
    //ap::get_first_time_node(node_copy, time_node);
    // getting time node
    vector<string> time_vars = global_config.time_var_name;
    time_vars.push_back(global_config.sample_time);
    pdrh::get_first_node_by_value(node_copy, time_node, time_vars);
    pdrh::delete_node(node_copy);
    capd::interval result(0);
    // checking if the time node is not empty
    if(!pdrh::is_node_empty(time_node))
    {
        // checking if the time node signature is <var>=<value>
        if(time_node->value == "=")
        {
            if(time_node->operands.front()->value == global_config.sample_time)
            {
                result = pdrh2box::node_to_interval(time_node->operands.back());
                pdrh::delete_node(time_node);
                return result;
            }
            if(time_node->operands.back()->value == global_config.sample_time)
            {
                result = pdrh2box::node_to_interval(time_node->operands.front());
                pdrh::delete_node(time_node);
                return result;
            }
        }
    }
    pdrh::delete_node(time_node);
    return capd::interval(0.0);
}

capd::interval ap::get_sample_rate(pdrh::mode* m)
{
    for(pdrh::mode::jump j : m->jumps)
    {
        capd::interval sample_rate = ap::get_sample_rate(j.guard);
        if(sample_rate != capd::interval(0.0))
        {
            return sample_rate;
        }
    }
    return capd::interval(0.0);
}

// using only the front box here !!!
capd::interval ap::get_meal_time(pdrh::node *n, vector<box> boxes)
{
    auto *node_copy = new pdrh::node();
    pdrh::copy_tree(node_copy, n);
    auto* time_node = new pdrh::node;
    //ap::get_first_time_node(node_copy, time_node);
    // getting time node
    vector<string> time_vars = global_config.time_var_name;
    time_vars.push_back(global_config.sample_time);
    pdrh::get_first_node_by_value(node_copy, time_node, time_vars);
    pdrh::delete_node(node_copy);
    capd::interval result(0);
    // checking if the time node is not empty
    if(!pdrh::is_node_empty(time_node))
    {
        // checking if the time node signature is <var>=<value>
        if(time_node->value == "=")
        {
            if(time_node->operands.front()->value == "tau")
            {
                result = pdrh2box::node_to_interval(time_node->operands.back(), boxes);
                pdrh::delete_node(time_node);
                return result;
            }
            if(time_node->operands.back()->value == "tau")
            {
                result = pdrh2box::node_to_interval(time_node->operands.front(), boxes);
                pdrh::delete_node(time_node);
                return result;
            }
        }
    }
    pdrh::delete_node(time_node);
    return capd::interval(0.0);
}

capd::interval ap::get_meal_time(pdrh::mode *m, vector<box> boxes)
{
    for(pdrh::mode::jump j : m->jumps)
    {
        capd::interval meal_time = ap::get_meal_time(j.guard, boxes);
        if(meal_time != capd::interval(0.0))
        {
            return meal_time;
        }
    }
    return capd::interval(0.0);
}

int ap::jumps_per_mode(pdrh::mode *m, vector<box> boxes)
{
    capd::interval sample_rate = ap::get_sample_rate(m);
    for(pdrh::state st : pdrh::goal)
    {
        if(m->id == st.id)
        {
            return ceil((ap::get_meal_time(st.prop, boxes) / sample_rate).rightBound());
        }
    }
    return ceil((ap::get_meal_time(m, boxes) / sample_rate).rightBound());
}

int ap::jumps_per_mode(pdrh::mode *cur_mode, pdrh::mode *prev_mode, vector<box> boxes)
{
    capd::interval left_over;
    // checking if there is previous mode
    if(prev_mode->id > 0)
    {
        capd::interval sample_rate_prev_mode = ap::get_sample_rate(prev_mode);
        capd::interval meal_time_prev_mode = ap::get_meal_time(prev_mode, boxes);
        left_over = capd::interval(fmod(meal_time_prev_mode.leftBound(), sample_rate_prev_mode.leftBound()),
                fmod(meal_time_prev_mode.rightBound(), sample_rate_prev_mode.rightBound()));
    }
    else
    {
        left_over = capd::interval(0);
    }

    capd::interval sample_rate_cur_mode = ap::get_sample_rate(cur_mode);
    for(pdrh::state st : pdrh::goal)
    {
        if(cur_mode->id == st.id)
        {
            return ceil(((ap::get_meal_time(st.prop, boxes) + left_over) / sample_rate_cur_mode).rightBound());
        }
    }
    return ceil(((ap::get_meal_time(cur_mode, boxes) + left_over) / sample_rate_cur_mode).rightBound());
}

bool ap::accept_path(vector<pdrh::mode *> path, vector<box> boxes)
{
    int pos = 0;
    // creating an empty mode
    auto *prev_mode = new pdrh::mode;
    prev_mode->id = 0;
    while(pos < path.size())
    {
        pdrh::mode *cur_mode = path.at(pos);
        int num_reps = 1;
        for(int i = pos + 1; i < path.size(); i++)
        {
            if(path.at(i)->id == cur_mode->id)
            {
                num_reps++;
            }
            else
            {
                break;
            }
        }
        int num_jumps = 0;
        if(prev_mode->id == 0)
        {
            num_jumps = ap::jumps_per_mode(cur_mode, boxes);
        }
        else
        {
            num_jumps = ap::jumps_per_mode(cur_mode, prev_mode, boxes);
        }
        //cout << "Num reps: " << num_reps << endl;
        //cout << "Num jumps: " << num_jumps << endl;
        if(num_reps != num_jumps)
        {
            return false;
        }
        pos += num_reps;
        prev_mode = cur_mode;
    }
    delete prev_mode;
    return true;
}

box ap::solve_odes(map<string, pdrh::node *> odes, box init, capd::interval time, vector<box> boxes)
{
    // creating capd string here
    // declaring parameters
    string par_string = "par:";
    for(box b : boxes)
    {
        map<string, capd::interval> b_map = b.get_map();
        for(auto & it : b_map)
        {
            par_string += it.first + ',';
        }
        //cout << b << endl;
    }
    par_string.back() = ';';

    // declaring variables
    string var_string = "var:";
    string fun_string = "fun:";
    int odes_size = 0;
    for(auto & ode : odes)
    {
        if((pdrh::par_map.find(ode.first) == pdrh::par_map.end()) &&
            (pdrh::rv_map.find(ode.first) == pdrh::rv_map.end()) &&
            (pdrh::dd_map.find(ode.first) == pdrh::dd_map.end()))
        {
            var_string += ode.first + ',';
            fun_string += pdrh::node_to_string_infix(ode.second) + ',';
            odes_size++;
        }
    }
    var_string.back() = ';';
    fun_string.back() = ';';
//    cout << "Solving ODEs: " << par_string + var_string + fun_string << endl;


//    cout << par_string << endl;
//    cout << var_string << endl;
//    cout << fun_string << endl;

    // creating an ODE solver and setting precision
    capd::IMap vectorField(par_string + var_string + fun_string);
    capd::IOdeSolver solver(vectorField, 20);
    solver.setAbsoluteTolerance(1e-12);
    solver.setRelativeTolerance(1e-12);
    capd::ITimeMap timeMap(solver);

    //setting parameter values
    for(const box& b : boxes)
    {
        map<string, capd::interval> b_map = b.get_map();
        for(auto & it : b_map)
        {
            vectorField.setParameter(it.first, it.second);
        }
    }

    // setting initial condition here
    capd::IVector c(odes_size);
    map<string, capd::interval> init_map = init.get_map();
    int i = 0;
    for(auto & it : init_map)
    {
        c[i] = it.second;
        i++;
    }
    capd::C0HORect2Set s(c);

    // solving the ODE system and creating the result
    capd::IVector result = timeMap(time, s);
    map<string, capd::interval> res_map;
    i = 0;
    for(auto & ode : odes)
    {
        if((pdrh::par_map.find(ode.first) == pdrh::par_map.end()) &&
           (pdrh::rv_map.find(ode.first) == pdrh::rv_map.end()) &&
           (pdrh::dd_map.find(ode.first) == pdrh::dd_map.end()))
        {
            res_map.insert(make_pair(ode.first, result[i]));
            i++;
        }
    }
    return {res_map};
}

// boxes - vector of parameter boxes, init - initial box, time - time horizon
box ap::solve_odes_nonrig(map<string, pdrh::node *> odes, box init, capd::interval time, vector<box> boxes)
{
    // creating capd string here
    // declaring parameters
    string par_string = "par:";
    for(const box& b : boxes)
    {
        map<string, capd::interval> b_map = b.get_map();
        for(auto & it : b_map)
        {
            par_string += it.first + ',';
        }
        //cout << b << endl;
    }
    par_string.back() = ';';

    // declaring variables
    string var_string = "var:";
    string fun_string = "fun:";
    int odes_size = 0;
    for(auto it = odes.begin(); it != odes.end(); it++)
    {
        if((pdrh::par_map.find(it->first) == pdrh::par_map.end()) &&
           (pdrh::rv_map.find(it->first) == pdrh::rv_map.end()) &&
           (pdrh::dd_map.find(it->first) == pdrh::dd_map.end()))
        {
            var_string += it->first + ',';
            fun_string += pdrh::node_to_string_infix(it->second) + ',';
            odes_size++;
        }
    }
    var_string.back() = ';';
    fun_string.back() = ';';

//    cout << par_string << endl;
//    cout << var_string << endl;
//    cout << fun_string << endl;

    // creating an ODE solver and setting precision
    capd::DMap vectorField(par_string + var_string + fun_string);
    capd::DOdeSolver solver(vectorField, 20);
//    solver.setAbsoluteTolerance(1e-12);
//    solver.setRelativeTolerance(1e-12);
    capd::DTimeMap timeMap(solver);
    solver.setStep(time.rightBound());

    //setting parameter values
    for(box b : boxes)
    {
        map<string, capd::interval> b_map = b.get_map();
        for(auto it = b_map.begin(); it != b_map.end(); it++)
        {
            vectorField.setParameter(it->first, it->second.rightBound());
        }
    }

    // setting initial condition here
    capd::DVector c(odes_size), result(odes_size);
    map<string, capd::interval> init_map = init.get_map();
    int i = 0;
    for(auto it = init_map.begin(); it != init_map.end(); it++)
    {
        c[i] = it->second.rightBound();
        i++;
    }
    //capd::C0HORect2Set s(c);

    // solving the ODE system and creating the result
    result = timeMap(time.rightBound(), c);
    map<string, capd::interval> res_map;
    i = 0;
    for(auto it = odes.begin(); it != odes.end(); it++)
    {
        if((pdrh::par_map.find(it->first) == pdrh::par_map.end()) &&
           (pdrh::rv_map.find(it->first) == pdrh::rv_map.end()) &&
           (pdrh::dd_map.find(it->first) == pdrh::dd_map.end()))
        {
            res_map.insert(make_pair(it->first, result[i]));
            i++;
        }
    }
//    cout << "ODE Solution" << endl;
//    cout << box(res_map) << endl;
    return box(res_map);
}

// boxes - vector of parameter boxes, init - initial box, time - time horizon
box ap::solve_odes_discrete(map<string, pdrh::node *> odes, box init, capd::interval time, size_t num_points, vector<box> boxes)
{
    // creating capd string here
    // declaring parameters
    string par_string = "par:";
    for(box b : boxes)
    {
        map<string, capd::interval> b_map = b.get_map();
        for(auto it = b_map.begin(); it != b_map.end(); it++)
        {
            par_string += it->first + ',';
        }
//        cout << b << endl;
    }
    par_string.back() = ';';

    // declaring variables
    string var_string = "var:";
    string fun_string = "fun:";
    int odes_size = 0;
    for(auto it = odes.begin(); it != odes.end(); it++)
    {
        if((pdrh::par_map.find(it->first) == pdrh::par_map.end()) &&
           (pdrh::rv_map.find(it->first) == pdrh::rv_map.end()) &&
           (pdrh::dd_map.find(it->first) == pdrh::dd_map.end()))
        {
            var_string += it->first + ',';
            fun_string += pdrh::node_to_string_infix(it->second) + ',';
            odes_size++;
        }
    }
    var_string.back() = ';';
    fun_string.back() = ';';

//    cout << par_string << endl;
//    cout << var_string << endl;
//    cout << fun_string << endl;

    // creating an ODE solver and setting precision
    capd::DMap odes_rhs(par_string + var_string + fun_string);

    //setting parameter values
    for(box b : boxes)
    {
        map<string, capd::interval> b_map = b.get_map();
        for(auto it = b_map.begin(); it != b_map.end(); it++)
        {
            odes_rhs.setParameter(it->first, it->second.rightBound());
        }
    }

    // setting initial condition here
    capd::DVector init_vector(odes_size), res_vector(odes_size);
    map<string, capd::interval> init_map = init.get_map();
    size_t i = 0;
    for(auto it = init_map.begin(); it != init_map.end(); it++)
    {
        init_vector[i] = it->second.rightBound();
        i++;
    }

    // solving the ode system using discretisation over num_points time points
    for(size_t i = 0; i < num_points; i++)
    {
        res_vector = odes_rhs(init_vector) * time.rightBound() / num_points;
        init_vector = init_vector + res_vector;
    }

    // solving the ODE system and creating the result
    map<string, capd::interval> res_map;
    i = 0;
    for(auto it = odes.begin(); it != odes.end(); it++)
    {
        if((pdrh::par_map.find(it->first) == pdrh::par_map.end()) &&
           (pdrh::rv_map.find(it->first) == pdrh::rv_map.end()) &&
           (pdrh::dd_map.find(it->first) == pdrh::dd_map.end()))
        {
            res_map.insert(make_pair(it->first, init_vector[i]));
            i++;
        }
    }
//    cout << "ODE Solution (Discretised)" << endl;
//    cout << init + box(res_map) << endl;
    return box(res_map);
}

capd::interval time_to_goal(pdrh::mode *m, vector<box> boxes)
{
    for(pdrh::state st : pdrh::goal)
    {
        if(m->id == st.id)
        {
            return ap::get_meal_time(st.prop, boxes);
        }
    }
}

int ap::simulate_path(vector<pdrh::mode *> path, box init, vector<box> boxes)
{
    // reachability depth == 0
    if(path.size() == 1)
    {
        return decision_procedure::check_invariants(path.front(), time_to_goal(path.front(), boxes), init, boxes, global_config.solver_bin, global_config.solver_opt);
    }
    // reachability depth > 0
    vector<box> sol_box;
    vector<box> init_box = {init};

//    cout << "Init box:" << endl;
//    cout << init_box << endl;
//    cout << "------" << endl;
//    int dummy;
//    cin >> dummy;

    capd::interval cur_mode_time(0);
    capd::interval prev_mode_time(0);
    int window_size = 1;
//    #pragma omp critical
//    cout << "Window size: " << window_size << endl;
    //CLOG_IF(global_config.verbose, INFO, "algorithm") << "Window size: " << window_size;
//    size_t sat_num = 0;
//    size_t unsat_num = 0;
//    size_t undet_num = 0;

    // going through all modes in the path
    for(size_t j = 0; j < path.size() - 1; j = j + window_size)
    {
        // applying the window of size window_size
        for(size_t i = j; (i < j + window_size) && (i < path.size() - 1); i++)
        {
            pdrh::mode *cur_mode = path.at(i);
            pdrh::mode *next_mode = path.at(i + 1);
            capd::interval time;

            // solving odes and invariants check
            if(cur_mode->id == next_mode->id)
            {
                time = ap::get_sample_rate(cur_mode) - prev_mode_time;
                cur_mode_time += time;
                prev_mode_time = capd::interval(0);
            }
            else
            {
                time = ap::get_meal_time(cur_mode, boxes) - cur_mode_time;
                cur_mode_time = capd::interval(0);
                prev_mode_time = time;
            }
            // checking the invariants
            box init_box_hull = box_factory::box_hull(init_box);
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Init box (VERIFIED) in mode " << cur_mode->id << " for depth " << i;
            CLOG_IF(global_config.verbose, INFO, "algorithm") << init_box_hull;
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Integration time: " << time;
//            cout << "----------" << endl;
            //if(i == 20) exit(EXIT_FAILURE);

            int invt_check = decision_procedure::UNSAT;
            if(ap::check_invariants(cur_mode, init_box_hull, boxes))
            {
                invt_check = decision_procedure::check_invariants(cur_mode, time, init_box_hull, boxes, global_config.solver_bin, global_config.solver_opt);
            }
            //int invt_check = decision_procedure::SAT;
            switch(invt_check)
            {
                case decision_procedure::SAT:
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Invariant is SAT in mode " << cur_mode->id << " @ depth=" << i;
                    break;

                case decision_procedure::UNDET:
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Invariant is UNDET in mode " << cur_mode->id << " @ depth=" << i;
                    return decision_procedure::UNDET;

                case decision_procedure::UNSAT:
                    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Invariant is UNSAT in mode " << cur_mode->id << " @ depth=" << i;
                    return decision_procedure::UNSAT;
            }
            // solving odes
            for(size_t k = 0; k < init_box.size(); k++)
            {
                sol_box.push_back(solve_odes(cur_mode->odes, init_box.at(k), time, boxes));
                //sol_box.push_back(solve_odes_nonrig(cur_mode->odes, init_box.at(k), time, boxes));
            }
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Solution (VERIFIED) box in mode " << cur_mode->id << " at depth = " << i;
            CLOG_IF(global_config.verbose, INFO, "algorithm") << box_factory::box_hull(sol_box);
//            cout << "===========" << endl;

//            cout << "Solution box hull in mode " << cur_mode->id << " at depth = " << i << endl;
//            cout << box_factory::box_hull(sol_box) << endl;

//            #pragma omp critical
//            cout << "Total number of boxes so far: " << sol_box.size() << endl;
            vector<box> part_sol_box;
            for(box b : sol_box)
            {
                vector<box> part_boxes = box_factory::bisect(b, vector<string>{"e"});
                part_sol_box.insert(part_sol_box.end(), part_boxes.begin(), part_boxes.end());
            }

            // resetting the initial state for the next mode
            init_box.clear();
            map<string, pdrh::node*> reset_map = cur_mode->get_jump(next_mode->id).reset;
            for(box b : part_sol_box)
            {
//                map<string, capd::interval> init_map;
//                for (auto it = reset_map.begin(); it != reset_map.end(); it++)
//                {
//                    if((pdrh::par_map.find(it->first) == pdrh::par_map.end()) &&
//                       (pdrh::rv_map.find(it->first) == pdrh::rv_map.end()) &&
//                       (pdrh::dd_map.find(it->first) == pdrh::dd_map.end()))
//                    {
//                        vector<box> reset_boxes = boxes;
//                        reset_boxes.push_back(b);
//                        init_map.insert(make_pair(it->first, pdrh::node_to_interval(it->second, reset_boxes)));
//                    }
//                }
//                // can add random error here
//                init_box.push_back(box(init_map));
                init_box.push_back(ap::apply_reset(cur_mode->get_jump(next_mode->id).reset, b, boxes));
            }
            // clear solution boxes
            sol_box.clear();
            part_sol_box.clear();
        }
        init_box = { box_factory::box_hull(init_box) };
    }
    // checking the invariants in the last mode
    box init_box_hull = box_factory::box_hull(init_box);
    capd::interval time = time_to_goal(path.back(), boxes) - cur_mode_time;
    int invt_check = decision_procedure::UNSAT;
    if(ap::check_invariants(path.back(), init_box_hull, boxes))
    {
        invt_check = decision_procedure::check_invariants(path.back(), time, init_box_hull, boxes, global_config.solver_bin, global_config.solver_opt);
    }
    switch(invt_check)
    {
        case decision_procedure::SAT:
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Invariant is SAT in mode " << path.back()->id << " @ depth=" << path.size() - 1;
            break;

        case decision_procedure::UNDET:
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Invariant is UNDET in mode " << path.back()->id << " at depth=" << path.size() - 1;
            return decision_procedure::UNDET;

        case decision_procedure::UNSAT:
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Invariant is UNSAT in mode " << path.back()->id << " at depth=" << path.size() - 1;
            return decision_procedure::UNSAT;
    }
    // computing solution for the goal
    for(size_t k = 0; k < init_box.size(); k++)
    {
        sol_box.push_back(solve_odes(path.back()->odes, init_box.at(k), time, boxes));
        //sol_box.push_back(solve_odes_nonrig(path.back()->odes, init_box.at(k), time, boxes));
    }
    return decision_procedure::SAT;
}

box ap::compute_objective(vector<pdrh::mode *> path, box init, vector<box> boxes, vector<string> obj_name)
{
    // reachability depth == 0
    if(path.size() == 1)
    {
        box sol = solve_odes(path.front()->odes, init, time_to_goal(path.front(), boxes), boxes);
        map<string, capd::interval> obj_map, b_map;
        b_map = sol.get_map();
        for(auto it = b_map.begin(); it != b_map.end(); it++)
        {
            if(find(obj_name.begin(), obj_name.end(), it->first) != obj_name.end())
            {
                obj_map.insert(make_pair(it->first, it->second));
            }
        }
        return box(obj_map);
    }

    box sol;
    capd::interval cur_mode_time(0);
    capd::interval prev_mode_time(0);
    int window_size = 1;

    box domain = pdrh2box::get_domain();

    // going through all modes in the path
    for(size_t j = 0; j < path.size() - 1; j = j + window_size)
    {
        // applying the window of size window_size
        for(size_t i = j; (i < j + window_size) && (i < path.size() - 1); i++)
        {
            pdrh::mode *cur_mode = path.at(i);
            pdrh::mode *next_mode = path.at(i + 1);
            capd::interval time;

            // solving odes and invariants check
            if(cur_mode->id == next_mode->id)
            {
                time = ap::get_sample_rate(cur_mode) - prev_mode_time;
                cur_mode_time += time;
                prev_mode_time = capd::interval(0);
            }
            else
            {
                time = ap::get_meal_time(cur_mode, boxes) - cur_mode_time;
                cur_mode_time = capd::interval(0);
                prev_mode_time = time;
            }




            // printing out the initial box
//            cout << "Init box (DICRETISED) for depth " << i << endl;
//            cout << init << endl;
//            cout << "----------" << endl;

            // solving odes
            //sol = solve_odes_nonrig(cur_mode->odes, init, time, boxes);
            sol = solve_odes(cur_mode->odes, init, time, boxes);
            cout << "Solution @ step " << i << " in mode " << cur_mode->id << ": " << endl << sol << endl;
//            capd::interval jump_time  = decision_procedure::get_jump_time(cur_mode, init, boxes);
//            if(jump_time.leftBound() != -1)
//            {
//                cout << "Jump time: " << decision_procedure::get_jump_time(cur_mode, init, boxes) << endl;
//                exit(EXIT_SUCCESS);
//            }
//            cout << "====================" << endl;
            //sol = solve_odes_discrete(cur_mode->odes, init, time, 100, boxes);
            #pragma omp critical
            {
//                cout << "====================" << endl;
//                cout << "Solution of the ODE system: " << sol << endl;
//                cout << "--------------------" << endl;
//                cout << "The domain of system variables: " << domain << endl;
//                cout << "--------------------" << endl;
//                if(domain.contains(sol))
//                {
//                    cout << "The solution is inside the domain" << endl;
//                }
//                else
//                {
//                    cout << "The solution is outside the domain" << endl;
//                }
//                cout << endl;
            }

            if(!domain.contains(sol))
            {
                return box();
            }

            // printing out the solution box
//            cout << "Solution (DICRETISED) box for depth " << i << endl;
//            cout << sol << endl;
//            cout << "===========" << endl;

            map<string, pdrh::node*> reset_map = cur_mode->get_jump(next_mode->id).reset;

            map<string, capd::interval> init_map;
            vector<box> reset_boxes = boxes;
            reset_boxes.push_back(sol);
            for (auto it = reset_map.begin(); it != reset_map.end(); it++)
            {
                if((pdrh::par_map.find(it->first) == pdrh::par_map.end()) &&
                   (pdrh::rv_map.find(it->first) == pdrh::rv_map.end()) &&
                   (pdrh::dd_map.find(it->first) == pdrh::dd_map.end()))
                {
                    init_map.insert(make_pair(it->first, pdrh2box::node_to_interval(it->second, reset_boxes)));
                }
            }
            // can add random error here
            init = box(init_map);
        }
    }
    // checking the invariants in the last mode
    capd::interval time = time_to_goal(path.back(), boxes) - cur_mode_time;
    // computing solution for the goal
    //sol = solve_odes_nonrig(path.back()->odes, init, time, boxes);
    sol = solve_odes(path.back()->odes, init, time, boxes);
    cout << "Final solution at mode " << path.back()->id << ": " << endl << sol << endl;
    map<string, capd::interval> obj_map, b_map;
    b_map = sol.get_map();
    for(auto it = b_map.begin(); it != b_map.end(); it++)
    {
        if(find(obj_name.begin(), obj_name.end(), it->first) != obj_name.end())
        {
            obj_map.insert(make_pair(it->first, it->second));
        }
    }
    return box(obj_map);
}

capd::interval ap::compute_robustness(vector<pdrh::mode *> path, box init, vector<box> boxes)
{
    // overall robustness over the path
    capd::interval min_rob(numeric_limits<double>::max());

    // reachability depth == 0
    if(path.size() == 1)
    {
        box sol = solve_odes_nonrig(path.front()->odes, init, time_to_goal(path.front(), boxes), boxes);

//        cout << "Solution @ 0: " << sol << endl;
//        cout << "----------" << endl;
//
//        cout << "There are " << path.front()->invts.size() << " invariants to check:" << endl;
        for(pdrh::node* n : path.front()->invts)
        {
//            cout << "Evaluating invariant : " << pdrh::node_to_string_infix(n) << endl;
            if(n->value != ">=" || n->operands.size() > 2 || n->operands.back()->value != "0")
            {
                ostringstream s;
                s << "Please rewrite the invariant \"" << pdrh::node_to_string_infix(n) << "\" in supported format";
                throw invalid_argument(s.str());
            }
//            cout << "Representation: OK" << endl;
            capd::interval rob = pdrh2box::node_to_interval(n->operands.front(), {sol, boxes});
//            cout << "Invariant robustness: " << rob << endl;
            if(rob < min_rob)
            {
                min_rob = rob;
            }
        }
//        cout << "Overall mode robustness: " << min_rob << endl;
//        cout << "==========" << endl << endl;
        return min_rob;
    }

    box sol;
    capd::interval cur_mode_time(0);
    capd::interval prev_mode_time(0);
    int window_size = 1;

    //capd::interval sample_rate(5);

    // going through all modes in the path
    for(size_t j = 0; j < path.size() - 1; j = j + window_size)
    {
        // applying the window of size window_size
        for(size_t i = j; (i < j + window_size) && (i < path.size() - 1); i++)
        {
            pdrh::mode *cur_mode = path.at(i);
            pdrh::mode *next_mode = path.at(i + 1);
            capd::interval time;

            // solving odes and invariants check
            if(cur_mode->id == next_mode->id)
            {
                time = ap::get_sample_rate(cur_mode) - prev_mode_time;
                //time = sample_rate - prev_mode_time;
                cur_mode_time += time;
                prev_mode_time = capd::interval(0);
            }
            else
            {
                time = ap::get_meal_time(cur_mode, boxes) - cur_mode_time;
                //time = sample_rate - cur_mode_time;
                cur_mode_time = capd::interval(0);
                prev_mode_time = time;
            }

            // solving odes
            //sol = solve_odes_nonrig(cur_mode->odes, init, time, boxes);
            sol = solve_odes_discrete(cur_mode->odes, init, time, global_config.ode_discretisation, boxes);
            //sol = init;
//            cout << "Solution @ " << i << ": " << sol << endl;
//            cout << "----------" << endl;
//
//            cout << "There are " << cur_mode->invts.size() << " invariants to check:" << endl;
            for(pdrh::node* n : cur_mode->invts)
            {
//                cout << "Evaluating invariant : " << pdrh::node_to_string_infix(n) << endl;
                if(n->value != ">=" || n->operands.size() > 2 || n->operands.back()->value != "0")
                {
                    ostringstream s;
                    s << "Please rewrite the invariant \"" << pdrh::node_to_string_infix(n) << "\" in supported format";
                    throw invalid_argument(s.str());
                }
//                cout << "Representation: OK" << endl;
                capd::interval rob = pdrh2box::node_to_interval(n->operands.front(), {sol, boxes});
//                cout << "Invariant robustness: " << rob << endl;
                if(rob < min_rob)
                {
                    min_rob = rob;
                }
            }
//            cout << "Overall mode robustness: " << min_rob << endl;
//            cout << "==========" << endl << endl;

            // printing out the solution box
//            cout << "Solution (DICRETISED) box for depth " << i << endl;
//            cout << sol << endl;
//            cout << "===========" << endl;

            map<string, pdrh::node*> reset_map = cur_mode->get_jump(next_mode->id).reset;

            map<string, capd::interval> init_map;
            vector<box> reset_boxes = boxes;
            reset_boxes.push_back(sol);
            for (auto it = reset_map.begin(); it != reset_map.end(); it++)
            {
                if((pdrh::par_map.find(it->first) == pdrh::par_map.end()) &&
                   (pdrh::rv_map.find(it->first) == pdrh::rv_map.end()) &&
                   (pdrh::dd_map.find(it->first) == pdrh::dd_map.end()))
                {
                    init_map.insert(make_pair(it->first, pdrh2box::node_to_interval(it->second, reset_boxes)));
                }
            }
            // can add random error here
            init = box(init_map);
        }
    }
    // checking the invariants in the last mode
    capd::interval time = time_to_goal(path.back(), boxes) - cur_mode_time;
    // computing solution for the goal
    sol = solve_odes_nonrig(path.back()->odes, init, time, boxes);
//    cout << "Solution @ " << path.size() << ": " << sol << endl;
//    cout << "----------" << endl;

//    cout << "There are " << path.back()->invts.size() << " invariants to check:" << endl;
    for(pdrh::node* n : path.back()->invts)
    {
//        cout << "Evaluating invariant : " << pdrh::node_to_string_infix(n) << endl;
        if(n->value != ">=" || n->operands.size() > 2 || n->operands.back()->value != "0")
        {
            ostringstream s;
            s << "Please rewrite the invariant \"" << pdrh::node_to_string_infix(n) << "\" in supported format";
            throw invalid_argument(s.str());
        }
//        cout << "Representation: OK" << endl;
        capd::interval rob = pdrh2box::node_to_interval(n->operands.front(), {sol, boxes});
//        cout << "Invariant robustness: " << rob << endl;
        if(rob < min_rob)
        {
            min_rob = rob;
        }
    }
//    cout << "Overall mode robustness: " << min_rob << endl;
//    cout << "==========" << endl << endl;
    return min_rob;
}

// maximum robustenss over a set of paths
capd::interval ap::compute_max_robustness(vector<vector<pdrh::mode *>> paths, box init, vector<box> boxes)
{
    capd::interval max_rob = compute_robustness(paths.front(), init, boxes);
    for(int i = 1; i < paths.size(); i++)
    {
        capd::interval rob = compute_robustness(paths.at(i), init, boxes);
        if(rob.rightBound() > max_rob.rightBound())
        {
            max_rob = rob;
        }
    }
    return max_rob;
}

// minimum robustness over a set of paths
capd::interval ap::compute_min_robustness(vector<vector<pdrh::mode *>> paths, box init, vector<box> boxes)
{
    capd::interval min_rob = compute_robustness(paths.front(), init, boxes);
    for(int i = 1; i < paths.size(); i++)
    {
        capd::interval rob = compute_robustness(paths.at(i), init, boxes);
        if(rob.leftBound() < min_rob.leftBound())
        {
            min_rob = rob;
        }
    }
    return min_rob;
}

bool ap::check_invariants(pdrh::mode *m, box b, vector<box> boxes)
{
    bool res = true;
    for(pdrh::node *n : m->invts)
    {
        res = res && pdrh2box::node_to_boolean(n, {boxes, b});
    }
    return res;
}

vector<vector<pdrh::mode*>> ap::get_all_paths(vector<box> boxes)
{
    // getting list of shortest paths
    vector<vector<pdrh::mode*>> paths;
    vector<vector<pdrh::mode*>> res;
    for(pdrh::state i : pdrh::init)
    {
        for(pdrh::state g : pdrh::goal)
        {
            //cout << "Init: " << i.id << " goal: " << g.id << endl;
            vector<pdrh::mode*> path = pdrh::get_shortest_path(pdrh::get_mode(i.id), pdrh::get_mode(g.id));
            if(path.size() > 0)
            {
                if(path.size() == 1)
                {
                    res.push_back(path);
                }
                else
                {
                    paths.push_back(path);
                }
            }
        }
    }
    //cout << "Number of paths: " << paths.size() << endl;
    // inserting self-loops in each path
    pdrh::mode* prev_mode = new pdrh::mode;
    prev_mode->id = 0;
    for(vector<pdrh::mode*> path : paths)
    {
        //cout << "Path:";
        //for(pdrh::mode* m : path) cout << m->id << " ";
        //cout << endl;
        vector<pdrh::mode*> new_path;
        new_path.push_back(path.front());
        for(size_t i = 0; i < path.size(); i++)
        {
            pdrh::mode* cur_mode = path[i];
            int num_jumps;
            if(i < path.size() - 1)
            {
                num_jumps = ap::jumps_per_mode(cur_mode, prev_mode, boxes);
            }
            else
            {
                num_jumps = ap::jumps_per_mode(cur_mode, boxes);
            }
            for(int j = 0; j < num_jumps; j++)
            {
                new_path.push_back(cur_mode);
            }
            prev_mode = cur_mode;
        }
        new_path.push_back(path[path.size()-1]);
        res.push_back(new_path);
//        cout << "Found a path: ";
//        for(pdrh::mode* m : new_path) cout << m->id << " ";
//        cout << endl;
    }
    prev_mode = NULL;
    delete prev_mode;
    return res;
}

bool ap::is_sample_jump(pdrh::mode::jump jump)
{
    return jump.guard->value == "=" &&
            jump.guard->operands.size() == 2 &&
            (jump.guard->operands.front()->value == global_config.sample_time ||
              jump.guard->operands.back()->value == global_config.sample_time);
}

int ap::verify(size_t min_depth, size_t max_depth, vector<box> boxes)
{
    // list of all evaluated paths, where each path consists is a sequence of pairs (<mode_id>, <init_value>)
    vector<vector<pair<int, box>>> paths = {{make_pair(pdrh::init.front().id, pdrh2box::init_to_box(boxes))}};
    // global time
    //capd::interval global_time = init.get_map()[global_config.global_time];
    vector<vector<pair<int, box>>> good_paths;
    bool undet_flag = false;
    // just several iterations here
    while(paths.size() > 0)
    {
        // copying the first path from the list
        vector<pair<int, box>> path = paths.front();
        //cout << "Number of jumps: " << path.size()-1 << endl;
        // removing the first path in the list
        paths.erase(paths.begin());
        // getting the current mode
        pdrh::mode* cur_mode = pdrh::get_mode(path.back().first);
        //cout << "Current mode: " << cur_mode->id << endl;
        // getting the initial condition for the current mode
        box init = path.back().second;
        //cout << "====================" << endl;
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Mode " << cur_mode->id << " Step " << (path.size() - 1);
        CLOG_IF(global_config.verbose, INFO, "algorithm") << init;
        // iterating through the jumps in the current mode and
        // recording all possible jumps with their times
        map<int, pair<capd::interval, box>> jumps_times;
        // getting global time
        capd::interval global_time = init.get_map()[global_config.global_time];
        //cout << "Path global time: " << global_time << endl;
        // check global time here. could be changed to goal statement later
        capd::interval glob_time_intersection;
        if(global_time >= pdrh2box::node_to_interval(pdrh::var_map[global_config.global_time].second) ||
                capd::intervals::intersection(global_time, pdrh2box::node_to_interval(pdrh::var_map[global_config.global_time].second), glob_time_intersection) ||
                    path.size() - 1 >= max_depth)
        {
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Global time limit has been reached in mode " << cur_mode->id;
            return decision_procedure::SAT;
        }
        // the case when no jumps can be made here
        if(cur_mode->jumps.size() == 0)
        {
            //cout << "Checking invariants in terminal mode " << cur_mode->id << endl;
            // getting the time bound for the current mode
            capd::interval time_bound = pdrh2box::node_to_interval(cur_mode->time.second);
            if(global_time + time_bound > pdrh2box::node_to_interval(pdrh::var_map[global_config.global_time].second))
            {
                time_bound = pdrh2box::node_to_interval(pdrh::var_map[global_config.global_time].second) - global_time;
            }
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Time bound: " << time_bound;
            //cout << "Initial condition: " << init << endl;
            int invt_check = decision_procedure::check_invariants(cur_mode, time_bound, init, boxes, dreal::solver_bin, global_config.solver_opt);
            switch(invt_check)
            {
                // returning SAT if global time is reached for the current path
                case decision_procedure::SAT:
                    if(global_time + time_bound>= pdrh2box::node_to_interval(pdrh::var_map[global_config.global_time].second) ||
                       capd::intervals::intersection(global_time + time_bound, pdrh2box::node_to_interval(pdrh::var_map[global_config.global_time].second), glob_time_intersection) ||
                            path.size() - 1 >= max_depth)
                    {
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Global time limit has been reached in mode " << cur_mode->id;
                        return decision_procedure::SAT;
                    }
                    break;

                case decision_procedure::UNDET:
                    //cout << "UNDET" << endl;
                    undet_flag = true;
                    //return decision_procedure::UNDET;
                    break;

                case decision_procedure::UNSAT:
                    //cout << "UNSAT" << endl;
                    //return decision_procedure::UNSAT;
                    break;
            }
        }
        // the case when there jumps in the current mode
        for(pdrh::mode::jump jump : cur_mode->jumps)
        {
            // finding out the time of the jump with the delta-sat witness from dReal
            //cout << "Initial value: " << path.back().second << endl;
            pair<capd::interval, box> jump_time = decision_procedure::get_jump_time(cur_mode, jump, init, boxes);
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Time of the jump to mode " << jump.next_id <<" : " << jump_time.first << "; witness: " << jump_time.second;
            //cout << "===============" << endl;
            // adding only those jumps which are enabled within the mode
            if(jump_time.first != capd::interval(-1))
            {
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "Checking invariants in mode " << cur_mode->id;
                //cout << "Initial condition: " << init << endl;
                int invt_check = decision_procedure::check_invariants(cur_mode, jump_time.first, init, boxes, global_config.solver_bin, global_config.solver_opt);
                // updating the jump times only if invariants hold
                switch(invt_check)
                {
                    case decision_procedure::SAT:
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "SAT";
                        if(global_time >= pdrh2box::node_to_interval(pdrh::var_map[global_config.global_time].second) ||
                           capd::intervals::intersection(global_time, pdrh2box::node_to_interval(pdrh::var_map[global_config.global_time].second), glob_time_intersection) ||
                           path.size() - 1 >= max_depth)
                        {
                            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Global time limit has been reached in mode " << cur_mode->id;
                            return decision_procedure::SAT;
                        }
                        jumps_times.insert(make_pair(jump.next_id, jump_time));
                        break;
                    case decision_procedure::UNDET:
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNDET";
                        //return decision_procedure::UNDET;
                        undet_flag = true;
                        break;

                    case decision_procedure::UNSAT:
                        CLOG_IF(global_config.verbose, INFO, "algorithm") << "UNSAT";
                        //return decision_procedure::UNSAT;
                        break;
                }
                //cout << "===============" << endl;
            }
            // check global time here !!!
        }
        //cout << "====================" << endl;
        pair<int, pair<capd::interval, box>> sample_jump;
        // removing the sampling jumps if there are other which are enabled in this mode
        if(jumps_times.size() > 1)
        {
            for(auto it = jumps_times.begin(); it != jumps_times.end(); it++)
            {
                if(is_sample_jump(cur_mode->get_jump(it->first)))
                {
                    sample_jump = make_pair(it->first, it->second);
                    jumps_times.erase(it->first);
                    break;
                }
            }
        }
        //cout << "Applying the resets" << endl;
        // need to apply sample reset somewhere here!!!
        // for each obtained jump finding the value when the jumps takes place
        for(auto it = jumps_times.begin(); it != jumps_times.end(); it++)
        {
            //box sol = solve_odes_discrete(cur_mode->odes, init, it->second, global_config.ode_discretisation, boxes);
            //box sol = solve_odes_nonrig(cur_mode->odes, init, it->second.leftBound(), boxes);
            //box sol = solve_odes(cur_mode->odes, init, it->second.first, boxes);
            box sol = it->second.second;
            //cout << "Solution box for the jump to mode " << it->first << endl;
            //cout << sol << endl;
            //cout << "===============" << endl;
            // checking if sampling and another jump happen at the same time
            capd::interval intersection;
            if(capd::intervals::intersection(sample_jump.second.second.get_map()[global_config.global_time], sol.get_map()[global_config.global_time], intersection))
            {
                // considering box hull here then
                sol = ap::apply_reset(cur_mode->get_jump(sample_jump.first).reset, box_factory::box_hull({sol, sample_jump.second.second}), boxes);
            }
            // applying the corresponding reset here
            init = ap::apply_reset(cur_mode->get_jump(it->first).reset, sol, boxes);
            vector<pair<int, box>> new_path = path;
            new_path.push_back(make_pair(it->first, init));
            if(new_path.size() - 1 <= max_depth) paths.push_back(new_path);
        }
    }
    // returning undet if there are no SAT paths and there is at least one UNDET
    if(undet_flag)
    {
        return decision_procedure::UNDET;
    }
    return decision_procedure::UNSAT;
}

box ap::apply_reset(map<string, pdrh::node*> reset_map, box sol, vector<box> boxes)
{
    // getting a random value here
    const gsl_rng_type *T;
    gsl_rng *r;
    gsl_rng_env_setup();
    T = gsl_rng_default;
    // creating random generator
    r = gsl_rng_alloc(T);
    // setting the seed
    gsl_rng_set(r, std::chrono::system_clock::now().time_since_epoch() / std::chrono::milliseconds(1));
    //double noise = gsl_ran_gaussian_ziggurat(r, global_config.noise_var);
    // adding noise to the right hand
//    cout << "Solution before noise: " << sol << endl;
//    cout << "--------------------" << endl;
    map<string, capd::interval> sol_map = sol.get_map();
//    sol_map["e_phi"] += gsl_ran_gaussian_ziggurat(r, global_config.noise_var);
//    sol_map["e_psi"] += gsl_ran_gaussian_ziggurat(r, global_config.noise_var);
//    sol_map["e_the"] += gsl_ran_gaussian_ziggurat(r, global_config.noise_var);
//    sol_map["e"] += gsl_ran_gaussian_ziggurat(r, global_config.noise_var);

    map<string, capd::interval> param_map = box(boxes).get_map();
    double noise = gsl_ran_gaussian_ziggurat(r, global_config.noise_var);
    CLOG_IF(global_config.verbose, INFO, "algorithm") << "Noise value added: " << noise;
    capd::interval sampling_rate = ap::get_sample_rate(pdrh::get_mode(1));
    sol_map["u"] += noise * (param_map["Kp"].leftBound() +
                                param_map["Kd"].leftBound()/sampling_rate.leftBound() +
                                    param_map["Ki"].leftBound()*sampling_rate.leftBound());
    sol_map["e_int"] += noise * param_map["Ki"].leftBound()*sampling_rate.leftBound();

    gsl_rng_free(r);
//    cout << "Noise: " << noise << endl;
//    cout << "--------------------" << endl;
    sol = box(sol_map);
//    cout << "Solution after noise: " << sol << endl;
//    cout << "====================" << endl;
    // applying the reset here
    map<string, capd::interval> init_map;
    vector<box> reset_boxes = boxes;
    reset_boxes.push_back(sol);
    for (auto it = reset_map.begin(); it != reset_map.end(); it++)
    {
        if((pdrh::par_map.find(it->first) == pdrh::par_map.end()) &&
           (pdrh::rv_map.find(it->first) == pdrh::rv_map.end()) &&
           (pdrh::dd_map.find(it->first) == pdrh::dd_map.end()))
        {
            init_map.insert(make_pair(it->first, pdrh2box::node_to_interval(it->second, reset_boxes)));
        }
    }
    return box(init_map);
}

int ap::simulate(size_t min_depth, size_t max_depth, vector<box> boxes)
{
    // list of all evaluated paths, where each path consists is a sequence of pairs (<mode_id>, <init_value>)
    vector<vector<pair<int, box>>> paths = {{make_pair(pdrh::init.front().id, pdrh2box::init_to_box(boxes))}};
    vector<vector<pair<int, box>>> good_paths;
    // continuing until there are no paths to simulate
    while(paths.size() > 0)
    {
        // copying the first path from the list
        vector<pair<int, box>> path = paths.front();
        //cout << "Number of steps in the path: " << path.size()-1 << endl;
        // removing the first path in the list
        paths.erase(paths.begin());
        // getting the current mode
        pdrh::mode* cur_mode = pdrh::get_mode(path.back().first);
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Current mode: " << cur_mode->id;
        // getting the initial condition for the current mode
        box init = path.back().second;
//        cout << "====================" << endl;
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Mode " << cur_mode->id << " Step " << path.size() - 1;
        CLOG_IF(global_config.verbose, INFO, "algorithm") << "Init: " << init;
//        cout << "====================" << endl;
        // will be iterating through the jumps in the current mode and
        // recording all possible jumps with their times
        // I MIGHT NOT NEED THE TIMES OF THE JUMPS
        map<int, pair<capd::interval, box>> jumps_times;
        //capd::interval sample_rate = ap::get_sample_rate(cur_mode);
        //cout << "Sampling rate: " << sample_rate << endl;
        capd::interval integration_step = pdrh2box::node_to_interval(cur_mode->time.second).rightBound()/global_config.ode_discretisation;
        //cout << "Integration step: " << integration_step << endl;
        // represents a jump due to sampling
        pair<int, pair<capd::interval, box>> sample_jump = make_pair(0, make_pair(capd::interval(0.0), box()));
        for(size_t i = 0; i < global_config.ode_discretisation; i++)
        {
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Checking invariants in mode " << cur_mode->id << " Step " << path.size() - 1;
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Initial condition: " << init;
            // checking invariants
            // NEED TO ACCOUNT FOR MULTIPLE PATHS DURING SIMULATION
            if(ap::check_invariants(cur_mode, init, boxes))
            {
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "Invariants: SAT";
                CLOG_IF(global_config.verbose, INFO, "algorithm") <<  "Initial state: " << init;
            }
            else
            {
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "Invariants: UNSAT";
                break;
                //return decision_procedure::UNSAT;
            }
            // checking if the time horizon is reached
            if(init.get_map()[global_config.global_time].leftBound() >= pdrh2box::node_to_interval(pdrh::var_map[global_config.global_time].second).rightBound() ||
                    path.size() - 1 >= max_depth)
            {
                vector<pair<int, box>> new_path = path;
                new_path.push_back(make_pair(cur_mode->id, init));
                good_paths.push_back(new_path);
                CLOG_IF(global_config.verbose, INFO, "algorithm") << "Global time limit has been reached in mode " << cur_mode->id;
                return decision_procedure::SAT;
            }
            // computing the solution here
            //cout << "Before solving ODEs" << endl;
            box sol = solve_odes_discrete(cur_mode->odes, init, integration_step, 1, boxes);
            //box sol = solve_odes_nonrig(cur_mode->odes, init, integration_step, boxes);
            //box sol = solve_odes(cur_mode->odes, init, integration_step, boxes);
            capd::interval cur_time = integration_step*(i+1);
            CLOG_IF(global_config.verbose, INFO, "algorithm") << "Solution at time " << cur_time << ": " << sol;
//            cout << "====================" << endl;
            // checking the jumps here
            //cout << "Evaluating jumps now" << endl;
            // processing the sample jump first if it exists
            for(pdrh::mode::jump jump : cur_mode->jumps)
            {
                if(ap::is_sample_jump(jump))
                {
                    //cout << "Checking (sampling) jump to mode " << jump.next_id;
                    if(pdrh2box::check_zero_crossing(jump.guard, boxes, init, sol))
                    {
                        sample_jump = make_pair(jump.next_id, make_pair(cur_time, ap::apply_reset(jump.reset, sol, boxes)));
                        //cout << ". Enabled at or before " << cur_time << endl;
                    }
                    else
                    {
                        //cout << ". Does not happen before or at " << cur_time << endl;
                    }
                    break;
                }
            }
            // evaluating the rest of the jumps
            for(pdrh::mode::jump jump : cur_mode->jumps)
            {
                // checking zero crossing only if the jump didn't take place
                if(jumps_times.find(jump.next_id) == jumps_times.end() && !ap::is_sample_jump(jump))
                {
                    //cout << "Checking jump to mode " << jump.next_id;
                    // checking if either of the jumps is enabled
                    if(pdrh2box::check_zero_crossing(jump.guard, boxes, init, sol))
                    {
                        // if sample jump is enabled as well then we apply the sampling reset first
                        if(sample_jump.first != 0)
                        {
                            sol = ap::apply_reset(cur_mode->get_jump(sample_jump.first).reset, sol, boxes);
                        }
                        // applying the corresponding reset
                        jumps_times.insert(make_pair(jump.next_id, make_pair(cur_time, ap::apply_reset(jump.reset, sol, boxes))));
                        //cout << ". Enabled at or before " << cur_time << endl;
                    }
                    else
                    {
                        //cout << ". Does not happen before or at " << cur_time << endl;
                    }
                }
            }
            //cout << "====================" << endl;
            // compute robustness only at sampling points
            init = sol;
        }
        // checking if any jumps apart from the sampling one are available
        if(jumps_times.empty())
        {
            // adding a sampling jump only if it has been enabled
            if(sample_jump.first != 0) jumps_times.insert(sample_jump);
        }
        //cout << "Total number of enabled jumps: " << jumps_times.size() << endl;
        // adding the paths to the set of all paths
        for(auto it = jumps_times.begin(); it != jumps_times.end(); it++)
        {
            //cout << "To mode " << it->first << " at time " << it->second.first << " with the initial condition: " << it->second.second << endl;
            // updating the set of paths
            vector<pair<int, box>> new_path = path;
            new_path.push_back(make_pair(it->first, it->second.second));
            paths.push_back(new_path);
        }
        //cout << "====================" << endl;
    }
    return decision_procedure::UNSAT;

//    cout << "There are " << good_paths.size() << " good paths" << endl;
//    for(vector<pair<int, box>> path : good_paths)
//    {
//        cout << "=================" << endl;
//        for(pair<int, box> p : path)
//        {
//            cout << p.first << " ";
//        }
//        cout << endl;
//        cout << path.back().second << endl;
//    }
//
//    cout << "The end" << endl;
}





