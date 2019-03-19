//
// Created by fedor on 12/06/18.
//

#include "pdrh2box.h"
#include "pdrh_config.h"
//#include <easylogging++.h>
#include <iomanip>
#include "ap.h"

using namespace std;

// throws exception in case if one of the terminal modes is not a number
// evaluates the value of arithmetic expression
bool pdrh2box::node_to_boolean(pdrh::node *expr, vector<box> boxes)
{
    // comparison operators
    if(expr->value == ">=")
    {
        return pdrh2box::node_to_interval(expr->operands.front(), boxes) >= pdrh2box::node_to_interval(expr->operands.back(), boxes);
    }
    else if(expr->value == ">")
    {
        return pdrh2box::node_to_interval(expr->operands.front(), boxes) > pdrh2box::node_to_interval(expr->operands.back(), boxes);
    }
    else if(expr->value == "=")
    {
        return pdrh2box::node_to_interval(expr->operands.front(), boxes) == pdrh2box::node_to_interval(expr->operands.back(), boxes);
    }
    else if(expr->value == "<")
    {
        return pdrh2box::node_to_interval(expr->operands.front(), boxes) < pdrh2box::node_to_interval(expr->operands.back(), boxes);
    }
    else if(expr->value == "<=")
    {
        return pdrh2box::node_to_interval(expr->operands.front(), boxes) <= pdrh2box::node_to_interval(expr->operands.back(), boxes);
    }
    else if(expr->value == "and")
    {
        bool res = true;
        for(pdrh::node* n : expr->operands)
        {
            res = res && pdrh2box::node_to_boolean(n, boxes);
        }
        return res;
    }
    else if(expr->value == "or")
    {
        bool res = true;
        for(pdrh::node* n : expr->operands)
        {
            res = res || pdrh2box::node_to_boolean(n, boxes);
        }
        return res;
    }
    else
    {
        cerr << "Unrecognised or unsupported operation \"" << expr->value << "\"";
        exit(EXIT_FAILURE);
    }
}

// throws exception in case if one of the terminal modes is not a number
// evaluates the value of arithmetic expression
bool pdrh2box::check_zero_crossing(pdrh::node *expr, vector<box> boxes, box first, box last)
{
    // comparison operators
    if(expr->value == ">=" || expr->value == ">" || expr->value == "=" || expr->value == "<" || expr->value == "<=")
    {
//        cout << "Beginning left: " << pdrh::node_to_interval(expr->operands.front(), {boxes, first}) << endl;
//        cout << "Beginning right: " << pdrh::node_to_interval(expr->operands.back(), {boxes, first}) << endl;
//        cout << "Beginning left-right: " << pdrh::node_to_interval(expr->operands.front(), {boxes, first}) -
//                                            pdrh::node_to_interval(expr->operands.back(), {boxes, first}) << endl;
//        cout << "End left: " << pdrh::node_to_interval(expr->operands.front(), {boxes, last}) << endl;
//        cout << "End right: " << pdrh::node_to_interval(expr->operands.back(), {boxes, last}) << endl;
//        cout << "End left-right: " << pdrh::node_to_interval(expr->operands.front(), {boxes, last}) -
//                                           pdrh::node_to_interval(expr->operands.back(), {boxes, last}) << endl;
        return (pdrh2box::node_to_interval(expr->operands.front(), {boxes, first}) - pdrh2box::node_to_interval(expr->operands.back(), {boxes, first})) *
               (pdrh2box::node_to_interval(expr->operands.front(), {boxes, last}) - pdrh2box::node_to_interval(expr->operands.back(), {boxes, last})) < 0;
    }
    else if(expr->value == "and")
    {
        bool res = true;
        for(pdrh::node* n : expr->operands)
        {
            res = res && pdrh2box::check_zero_crossing(n, boxes, first, last);
        }
    }
    else if(expr->value == "or")
    {
        bool res = true;
        for(pdrh::node* n : expr->operands)
        {
            res = res || pdrh2box::check_zero_crossing(n, boxes, first, last);
        }
    }
    else
    {
        cerr << "Unrecognised or unsupported operation \"" << expr->value << "\"";
        exit(EXIT_FAILURE);
    }
}

// throws exception in case if one of the terminal modes is not a number
// evaluates the value of arithmetic expression
capd::interval pdrh2box::node_to_interval(pdrh::node *expr, vector<box> boxes)
{
    // terminal node
    if(expr->operands.size() == 0)
    {
        for(box b : boxes)
        {
            map<string, capd::interval> b_map = b.get_map();
            if(b_map.find(expr->value) != b_map.end())
            {
                return b_map[expr->value];
            }
        }
        if(expr->value == "-infty")
        {
            return capd::interval(-numeric_limits<double>::max(), -numeric_limits<double>::max());
        }
        else if(expr->value == "infty")
        {
            return capd::interval(numeric_limits<double>::max(), numeric_limits<double>::max());
        }
        return capd::interval(expr->value, expr->value);
    }
    else if(expr->operands.size() > 2)
    {
//        for(node *n : expr->operands)
//        {
//            return pdrh::node_to_interval(n);
//        }
//        CLOG(ERROR, "model") << "The number of operands can't be greater than 2";
        exit(EXIT_FAILURE);
    }
    else
    {
        if(expr->value == "+")
        {
            if(expr->operands.size() == 1)
            {
                return pdrh2box::node_to_interval(expr->operands.front(), boxes);
            }
            else if(expr->operands.size() == 2)
            {
                return pdrh2box::node_to_interval(expr->operands.front(), boxes) + pdrh2box::node_to_interval(expr->operands.back(), boxes);
            }
        }
        else if(expr->value == "-")
        {
            if(expr->operands.size() == 1)
            {
                return capd::interval(-1.0) * pdrh2box::node_to_interval(expr->operands.front(), boxes);
            }
            else if(expr->operands.size() == 2)
            {
                return pdrh2box::node_to_interval(expr->operands.front(), boxes) - pdrh2box::node_to_interval(expr->operands.back(), boxes);
            }
        }
        else if(expr->value == "*")
        {
            return pdrh2box::node_to_interval(expr->operands.front(), boxes) * pdrh2box::node_to_interval(expr->operands.back(), boxes);
        }
        else if(expr->value == "/")
        {
            return pdrh2box::node_to_interval(expr->operands.front(), boxes) / pdrh2box::node_to_interval(expr->operands.back(), boxes);
        }
        else if(expr->value == "^")
        {
            return capd::intervals::power(pdrh2box::node_to_interval(expr->operands.front(), boxes), pdrh2box::node_to_interval(expr->operands.back(), boxes));
        }
        else if(expr->value == "sqrt")
        {
            return capd::intervals::sqrt(pdrh2box::node_to_interval(expr->operands.front(), boxes));
        }
        else if(expr->value == "abs")
        {
            return capd::intervals::iabs(pdrh2box::node_to_interval(expr->operands.front(), boxes));
        }
        else if(expr->value == "exp")
        {
            return capd::intervals::exp(pdrh2box::node_to_interval(expr->operands.front(), boxes));
        }
        else if(expr->value == "log")
        {
            return capd::intervals::log(pdrh2box::node_to_interval(expr->operands.front(), boxes));
        }
        else if(expr->value == "sin")
        {
            return capd::intervals::sin(pdrh2box::node_to_interval(expr->operands.front(), boxes));
        }
        else if(expr->value == "cos")
        {
            return capd::intervals::cos(pdrh2box::node_to_interval(expr->operands.front(), boxes));
        }
        else if(expr->value == "tan")
        {
            return capd::intervals::tan(pdrh2box::node_to_interval(expr->operands.front(), boxes));
        }
        else if(expr->value == "asin")
        {
            return capd::intervals::asin(pdrh2box::node_to_interval(expr->operands.front(), boxes));
        }
        else if(expr->value == "acos")
        {
            return capd::intervals::acos(pdrh2box::node_to_interval(expr->operands.front(), boxes));
        }
        else if(expr->value == "atan")
        {
            return capd::intervals::atan(pdrh2box::node_to_interval(expr->operands.front(), boxes));
        }
        else
        {
            cerr << "Unknown function \"" << expr->value << "\"";
            exit(EXIT_FAILURE);
        }
    }
}

// throws exception in case if one of the terminal modes is not a number
// evaluates the value of arithmetic expression
capd::interval pdrh2box::node_to_interval(pdrh::node *expr)
{
    return pdrh2box::node_to_interval(expr, {box()});
}

pdrh::node* pdrh2box::box_to_node(box b)
{
    pdrh::node *res = new pdrh::node();
    res->value = "and";
    map<string, capd::interval> b_map = b.get_map();
    for(auto it = b_map.begin(); it != b_map.end(); it++)
    {
        // adding left node
        pdrh::node *node_left = new pdrh::node();
        node_left->value = ">=";
        node_left->operands.push_back(new pdrh::node(it->first));
        stringstream ss;
        ss << std::setprecision(16) << it->second.leftBound();
        node_left->operands.push_back(new pdrh::node(ss.str()));
        res->operands.push_back(node_left);
        // adding right node
        pdrh::node *node_right = new pdrh::node();
        node_right->value = "<=";
        node_right->operands.push_back(new pdrh::node(it->first));
        ss.str("");
        ss << std::setprecision(16) << it->second.rightBound();
        node_right->operands.push_back(new pdrh::node(ss.str()));
        res->operands.push_back(node_right);
    }
    return res;
}


// domain of nondeterministic parameters
box pdrh2box::get_nondet_domain()
{
    map<std::string, capd::interval> m;
    for(auto it = pdrh::par_map.cbegin(); it != pdrh::par_map.cend(); it++)
    {
        m.insert(make_pair(it->first, capd::interval(pdrh2box::node_to_interval(it->second.first).leftBound(),
                                                     pdrh2box::node_to_interval(it->second.second).rightBound())));
    }
    return box(m);
}


// domain of system variables
box pdrh2box::get_domain()
{
    map<std::string, capd::interval> m;
    for(auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
    {
        m.insert(make_pair(it->first, capd::interval(pdrh2box::node_to_interval(it->second.first).leftBound(),
                                                     pdrh2box::node_to_interval(it->second.second).rightBound())));
    }
    return box(m);
}


// domain of parameters to synthesize
box pdrh2box::get_psy_domain()
{
    map<std::string, capd::interval> m;
    for(auto it = pdrh::syn_map.cbegin(); it != pdrh::syn_map.cend(); it++)
    {
        m.insert(make_pair(it->first, capd::interval(pdrh2box::node_to_interval(pdrh::var_map[it->first].first).leftBound(),
                                                     pdrh2box::node_to_interval(pdrh::var_map[it->first].second).rightBound())));
    }
    return box(m);
}


// getting a string representation of reachability formula in smt2 format for all combinations of initial and goal modes
string pdrh2box::reach_to_smt2(vector<pdrh::mode*> path, vector<box> boxes)
{
    stringstream s;
    // setting logic
    s << "(set-logic QF_NRA_ODE)" << endl;
    // declaring variables and defining bounds
    for(auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
    {
        s << "(declare-fun " << it->first << " () Real)" << endl;
        for(int i = 0; i < path.size(); i++)
        {
            s << "(declare-fun " << it->first << "_" << i << "_0 () Real)" << endl;
            s << "(declare-fun " << it->first << "_" << i << "_t () Real)" << endl;
            if(it->second.first->value != "-infty")
            {
                s << "(assert (>= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
                s << "(assert (>= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
            }
            if(it->second.second->value != "infty")
            {
                s << "(assert (<= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
                s << "(assert (<= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
            }
        }
    }
    // declaring time pdrh::node_fix_index(reset_it->second, step, "t")
    for(int i = 0; i < path.size(); i++)
    {
        s << "(declare-fun time_" << i << " () Real)" << endl;
        s << "(assert (>= time_" << i << " " << pdrh::node_fix_index(path.at(i)->time.first, i, "0") << "))" << endl;
        s << "(assert (<= time_" << i << " " << pdrh::node_fix_index(path.at(i)->time.second, i, "0") << "))" << endl;
    }
    // defining odes
    for(auto path_it = path.cbegin(); path_it != path.cend(); path_it++)
    {
        if(find(path.cbegin(), path_it, *path_it) == path_it)
        {
            s << "(define-ode flow_" << (*path_it)->id << " (";
            for(auto ode_it = (*path_it)->odes.cbegin(); ode_it != (*path_it)->odes.cend(); ode_it++)
            {
                s << "(= d/dt[" << ode_it->first << "] " << pdrh::node_to_string_prefix(ode_it->second) << ")";
            }
            s << "))" << endl;
        }
    }
    // defining the reachability formula
    s << "(assert (and " << endl;
    // defining initial states
    s << "(or ";
    for(pdrh::state st : pdrh::init)
    {
        if(st.id == path.front()->id)
        {
            s << "(" << pdrh::node_fix_index(st.prop, 0, "0") << ")" << endl;
        }
    }
    s << ")" << endl;
    // defining boxes bounds
    for(box b : boxes)
    {
        map<string, capd::interval> m = b.get_map();
        for(int i = 0; i < path.size(); i++)
        {
            for (auto it = m.cbegin(); it != m.cend(); it++)
            {
                s << "(>= " << it->first << "_" << i << "_0 " << it->second.leftBound() << ")" << endl;
                s << "(<= " << it->first << "_" << i << "_0 " << it->second.rightBound() << ")" << endl;
                s << "(>= " << it->first << "_" << i << "_t " << it->second.leftBound() << ")" << endl;
                s << "(<= " << it->first << "_" << i << "_t " << it->second.rightBound() << ")" << endl;
            }
        }
    }
    // defining trajectory
    int step = 0;
    for(pdrh::mode* m : path)
    {
        // defining integrals
        s << "(= [";
        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
        {
            s << ode_it->first << "_" << step << "_t ";
        }
        s << "] (integral 0.0 time_" << step << " [";
        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
        {
            s << ode_it->first << "_" << step << "_0 ";
        }
        s << "] flow_" << m->id << "))" << endl;
        // defining invariants
        for(pdrh::node* invt : m->invts)
        {
            s << "(forall_t " << m->id << " [0.0 time_" << step << "] " << pdrh::node_fix_index(invt, step, "t") << ")" << endl;
        }
        // checking the current depth
        if(step < path.size() - 1)
        {
            // defining jumps
            for (pdrh::mode::jump j : m->jumps)
            {
                // only the jumps to the next mode in the path
                if(j.next_id == path.at(step+1)->id)
                {
                    s << pdrh::node_fix_index(j.guard, step, "t") << endl;
                    for (auto reset_it = j.reset.cbegin(); reset_it != j.reset.cend(); reset_it++)
                    {
                        s << "(= " << reset_it->first << "_" << step + 1 << "_0 " <<
                          pdrh::node_fix_index(reset_it->second, step, "t") << ")";
                    }
                }
            }
        }
        step++;
    }
    // defining goal
    s << "(or ";
    for(pdrh::state st : pdrh::goal)
    {
        if(st.id == path.back()->id)
        {
            s << "(" << pdrh::node_fix_index(st.prop, path.size() - 1, "t") << ")";
        }
    }
    s << ")))" << endl;
    // final statements
    s << "(check-sat)" << endl;
    s << "(exit)" << endl;
    return s.str();
}


// USED
string pdrh2box::reach_c_to_smt2(vector<pdrh::mode*> path, vector<box> boxes)
{
    stringstream s;
    // setting logic
    s << "(set-logic QF_NRA_ODE)" << endl;
    // checking whether either of last jumps have a time node
//    pdrh::node* timed_node_neg;
//    for(pdrh::state st : pdrh::goal)
//    {
//        timed_node_neg = pdrh::get_time_node_neg(st.prop);
//        if(timed_node_neg)
//        {
//            break;
//        }
//    }
    // declaring variables and defining bounds
    for(auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
    {
        s << "(declare-fun " << it->first << " () Real)" << endl;
        for(int i = 0; i < path.size(); i++)
        {
            s << "(declare-fun " << it->first << "_" << i << "_0 () Real)" << endl;
            s << "(declare-fun " << it->first << "_" << i << "_t () Real)" << endl;
            if(it->second.first->value != "-infty")
            {
                s << "(assert (>= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
                s << "(assert (>= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
            }
            if(it->second.second->value != "infty")
            {
                s << "(assert (<= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
                s << "(assert (<= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
            }
        }
    }
    // declaring time
    for(int i = 0; i < path.size(); i++)
    {
        s << "(declare-fun time_" << i << " () Real)" << endl;
        s << "(assert (>= time_" << i << " " << pdrh::node_fix_index(path.at(i)->time.first, i, "0") << "))" << endl;
        s << "(assert (<= time_" << i << " " << pdrh::node_fix_index(path.at(i)->time.second, i, "0") << "))" << endl;
    }
    // declaring local time and bounds
    //if (!timed_node_neg)
    //{
    s << "(declare-fun local_time () Real)" << endl;
    for(unsigned long i = 0; i < path.size() - 1; i++)
    {
        s << "(declare-fun local_time_" << i << "_0 () Real)" << endl;
        s << "(declare-fun local_time_" << i << "_t () Real)" << endl;
        s << "(assert (= local_time_" << i << "_0 " << pdrh::node_fix_index(path.at(i)->time.first, i, "0") <<
          "))" << endl;
        s << "(assert (>= local_time_" << i << "_t " << pdrh::node_fix_index(path.at(i)->time.first, i, "0") <<
          "))" << endl;
        s << "(assert (<= local_time_" << i << "_t " << pdrh::node_fix_index(path.at(i)->time.second, i, "0") <<
          "))" << endl;
    }
    // last mode
    //s << "(declare-fun local_time () Real)" << endl;
    s << "(declare-fun local_time_" << path.size() - 1 << "_0 () Real)" << endl;
    s << "(declare-fun local_time_" << path.size() - 1 << "_t () Real)" << endl;
    s << "(assert (= local_time_" << path.size() - 1 << "_0 " << pdrh::node_fix_index(path.back()->time.first, path.size() - 1, "0") <<
      "))" << endl;
    s << "(assert (>= local_time_" << path.size() - 1 << "_t " << pdrh::node_fix_index(path.back()->time.first, path.size() - 1, "0") <<
      "))" << endl;
    s << "(assert (<= local_time_" << path.size() - 1 << "_t " << pdrh::node_fix_index(path.back()->time.second, path.size() - 1, "0") <<
      "))" << endl;
    //}
    // defining odes
    for(auto path_it = path.cbegin(); path_it != path.cend(); path_it++)
    {
        if(std::find(path.cbegin(), path_it, *path_it) == path_it)
        {
            s << "(define-ode flow_" << (*path_it)->id << " (";
            for(auto ode_it = (*path_it)->odes.cbegin(); ode_it != (*path_it)->odes.cend(); ode_it++)
            {
                s << "(= d/dt[" << ode_it->first << "] " << pdrh::node_to_string_prefix(ode_it->second) << ")";
            }
            // introducing local time if defined
            //if(!timed_node_neg)
            //{
            s << "(= d/dt[local_time] 1.0)";
            //}
            s << "))" << endl;
        }
    }
    // defining the negated reachability formula
    s << "(assert (and (and " << endl;
    // defining initial states
    s << "(or ";
    for(pdrh::state st : pdrh::init)
    {
        if(path.front()->id == st.id)
        {
            s << "(" << pdrh::node_fix_index(st.prop, 0, "0") << ")";
        }
    }
    s << ")" << endl;
    // defining boxes bounds
    for(box b : boxes)
    {
        map<string, capd::interval> m = b.get_map();
        for(int i = 0; i < path.size(); i++)
        {
            for (auto it = m.cbegin(); it != m.cend(); it++)
            {
                s << "(>= " << it->first << "_" << i << "_0 " << it->second.leftBound() << ")" << endl;
                s << "(<= " << it->first << "_" << i << "_0 " << it->second.rightBound() << ")" << endl;
                s << "(>= " << it->first << "_" << i << "_t " << it->second.leftBound() << ")" << endl;
                s << "(<= " << it->first << "_" << i << "_t " << it->second.rightBound() << ")" << endl;
            }
        }
    }
    // defining trajectory
    int step = 0;
    for(pdrh::mode* m : path)
    {
        // defining integrals
        s << "(= [";
        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
        {
            s << ode_it->first << "_" << step << "_t ";
        }
        // defining local time if enabled
        //if((step == path.size() - 1) && (!timed_node_neg))
        //if(!timed_node_neg)
        //{
        s << "local_time_" << step << "_t";
        //}
        s << "] (integral 0.0 time_" << step << " [";
        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
        {
            s << ode_it->first << "_" << step << "_0 ";
        }
        // defining local time if enabled
        //if((step == path.size() - 1) && (!timed_node_neg))
        //if(!timed_node_neg)
        //{
        s << "local_time_" << step << "_0";
        //}
        s << "] flow_" << m->id << "))" << endl;
        // defining invariants
        for(pdrh::node* invt : m->invts)
        {
            s << "(forall_t " << m->id << " [0.0 time_" << step << "] " << pdrh::node_fix_index(invt, step, "t") << ")" << endl;
        }
        // checking the current depth
        if(step < path.size() - 1)
        {
            // defining jumps
            for (pdrh::mode::jump j : m->jumps)
            {
                //cout << "Jumping from " << m->id << " to " << j.next_id << "(control " << path.at(step+1)->id << ")" << endl;
                if(j.next_id == path.at(step+1)->id)
                {
                    //cout << "Recording the jumping from " << m->id << " to " << j.next_id << "(control " << path.at(step+1)->id << ")" << endl;
                    s << pdrh::node_fix_index(j.guard, step, "t") << endl;
                    if (step < path.size() - 1)
                    {
                        for (auto reset_it = j.reset.cbegin(); reset_it != j.reset.cend(); reset_it++)
                        {
                            s << "(= " << reset_it->first << "_" << step + 1 << "_0 " <<
                              pdrh::node_fix_index(reset_it->second, step, "t") << ")";
                        }
                    }
                }
            }
        }
        step++;
    }
    s << ")";
    // defining goal
    s << "(and ";
    for(pdrh::state st : pdrh::goal)
    {
        if(path.back()->id == st.id)
        {
            pdrh::node* timed_node_neg = ap::get_time_node_neg(st.prop);
            if(!timed_node_neg)
            {
                // checking if there is a not in front of the guard predicate because dReal does not work nicely
                // with double negation
                s << "(= local_time_" << path.size() - 1 << "_t " << pdrh::node_fix_index(path.back()->time.second, path.size() - 1, "0") <<
                  ")" << endl;
                if(st.prop->value == "not")
                {
                    s << "(forall_t " << st.id << " [0 time_" << path.size() - 1 << "] (" <<
                      pdrh::node_fix_index(st.prop->operands.front(), path.size() - 1, "t") << "))";
                }
                    // transforming the negation of disjunction into the conjunction of negations
                else if(st.prop->value == "or")
                {
                    for(pdrh::node* n : st.prop->operands)
                    {
                        s << "(forall_t " << st.id << " [0 time_" << path.size() - 1 << "] (not " <<
                          pdrh::node_fix_index(n, path.size() - 1, "t") << "))";
                    }
                }
                else
                {
                    s << "(forall_t " << st.id << " [0 time_" << path.size() - 1 << "] (not " << pdrh::node_fix_index(st.prop, path.size() - 1, "t") << "))";
                }
            }
            else
            {
                s << pdrh::node_fix_index(timed_node_neg, path.size() - 1, "t");
                delete timed_node_neg;
            }
        }
    }
    s << ")))" << endl;
    // final statements
    s << "(check-sat)" << endl;
    s << "(exit)" << endl;
    return s.str();
}

// USED
string pdrh2box::reach_c_to_smt2(int depth, vector<pdrh::mode *> path, vector<box> boxes)
{
    if(depth == path.size() - 1)
    {
        return pdrh2box::reach_c_to_smt2(path, boxes);
    }
    else
    {
        stringstream s;
        // setting logic
        s << "(set-logic QF_NRA_ODE)" << endl;
        // checking whether either of last jumps have a time node
//        pdrh::node* timed_node_neg;
//        for(pdrh::mode::jump j : path.at(depth)->jumps)
//        {
//            timed_node_neg = pdrh::get_time_node_neg(j.guard);
//            if(timed_node_neg)
//            {
//                //cout << "Found timed node: " << pdrh::node_to_string_prefix(timed_node_neg) << endl;
//                break;
//            }
//        }
        // declaring variables and defining bounds
        for(auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++)
        {
            s << "(declare-fun " << it->first << " () Real)" << endl;
            for(int i = 0; i <= depth; i++)
            {
                s << "(declare-fun " << it->first << "_" << i << "_0 () Real)" << endl;
                s << "(declare-fun " << it->first << "_" << i << "_t () Real)" << endl;
                if(it->second.first->value != "-infty")
                {
                    s << "(assert (>= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
                    s << "(assert (>= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
                }
                if(it->second.second->value != "infty")
                {
                    s << "(assert (<= " << it->first << "_" << i << "_0 " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
                    s << "(assert (<= " << it->first << "_" << i << "_t " << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
                }
            }
        }
        // declaring time
        for(int i = 0; i <= depth; i++)
        {
            s << "(declare-fun time_" << i << " () Real)" << endl;
            s << "(assert (>= time_" << i << " " << pdrh::node_fix_index(path.at(i)->time.first, i, "0") << "))" << endl;
            s << "(assert (<= time_" << i << " " << pdrh::node_fix_index(path.at(i)->time.second, i, "0") << "))" << endl;
        }
        // declaring local time and bounds
//        if (!timed_node_neg)
//        {
        s << "(declare-fun local_time () Real)" << endl;
        //cout << "HERE" << endl;
        for(unsigned long i = 0; i < depth; i++)
        {
            s << "(declare-fun local_time_" << i << "_0 () Real)" << endl;
            s << "(declare-fun local_time_" << i << "_t () Real)" << endl;
            s << "(assert (= local_time_" << i << "_0 " << pdrh::node_fix_index(path.at(i)->time.first, i, "0") <<
              "))" << endl;
            s << "(assert (>= local_time_" << i << "_t " << pdrh::node_fix_index(path.at(i)->time.first, i, "0") <<
              "))" << endl;
            s << "(assert (<= local_time_" << i << "_t " << pdrh::node_fix_index(path.at(i)->time.second, i, "0") <<
              "))" << endl;
        }
        // last mode
        //s << "(declare-fun local_time () Real)" << endl;
        s << "(declare-fun local_time_" << depth << "_0 () Real)" << endl;
        s << "(declare-fun local_time_" << depth << "_t () Real)" << endl;
        s << "(assert (= local_time_" << depth << "_0 " << pdrh::node_fix_index(path.at(depth)->time.first, depth, "0") <<
          "))" << endl;
        s << "(assert (>= local_time_" << depth << "_t " << pdrh::node_fix_index(path.at(depth)->time.first, depth, "0") <<
          "))" << endl;
        s << "(assert (<= local_time_" << depth << "_t " << pdrh::node_fix_index(path.at(depth)->time.second, depth, "0") <<
          "))" << endl;
//        }
        // defining odes
        int step = 0;
        for(auto path_it = path.cbegin(); path_it != path.cend(); path_it++)
        {
            if(std::find(path.cbegin(), path_it, *path_it) == path_it)
            {
                s << "(define-ode flow_" << (*path_it)->id << " (";
                for(auto ode_it = (*path_it)->odes.cbegin(); ode_it != (*path_it)->odes.cend(); ode_it++)
                {
                    s << "(= d/dt[" << ode_it->first << "] " << pdrh::node_to_string_prefix(ode_it->second) << ")";
                }
                // introducing local time if defined
                //if((!timed_node_neg))
                //{
                s << "(= d/dt[local_time] 1.0)";
                //}
                s << "))" << endl;
            }
            if(step >= depth)
            {
                break;
            }
            step++;
        }
        // defining the negated reachability formula
        s << "(assert (and (and " << endl;
        // defining initial states
        s << "(or ";
        for(pdrh::state st : pdrh::init)
        {
            if(path.front()->id == st.id)
            {
                s << "(" << pdrh::node_fix_index(st.prop, 0, "0") << ")";
            }
        }
        s << ")" << endl;
        // defining boxes bounds
        for(box b : boxes)
        {
            map<string, capd::interval> m = b.get_map();
            for(int i = 0; i <= depth; i++)
            {
                for (auto it = m.cbegin(); it != m.cend(); it++)
                {
                    s << "(>= " << it->first << "_" << i << "_0 " << it->second.leftBound() << ")" << endl;
                    s << "(<= " << it->first << "_" << i << "_0 " << it->second.rightBound() << ")" << endl;
                    s << "(>= " << it->first << "_" << i << "_t " << it->second.leftBound() << ")" << endl;
                    s << "(<= " << it->first << "_" << i << "_t " << it->second.rightBound() << ")" << endl;
                }
            }
        }
        // defining trajectory
        for(int i = 0; i <= depth; i++)
        {
            pdrh::mode* m = path.at(i);
            // defining integrals
            s << "(= [";
            for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
            {
                s << ode_it->first << "_" << i << "_t ";
            }
            // defining local time if enabled
            //if(!timed_node_neg)
            //{
            s << "local_time_" << i << "_t";
            //}
            s << "] (integral 0.0 time_" << i << " [";
            for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
            {
                s << ode_it->first << "_" << i << "_0 ";
            }
            // defining local time if enabled
            //if(!timed_node_neg)
            //{
            s << "local_time_" << i << "_0";
            //}
            s << "] flow_" << m->id << "))" << endl;
            // defining invariants
            for(pdrh::node* invt : m->invts)
            {
                s << "(forall_t " << m->id << " [0.0 time_" << i << "] " << pdrh::node_fix_index(invt, i, "t") << ")" << endl;
            }
            // checking the current depth
            if(i < depth)
            {
                // defining jumps
                for (pdrh::mode::jump j : m->jumps)
                {
                    // getting only the jumps leading to the next mode in the path
                    if(j.next_id == path.at(i+1)->id)
                    {
                        s << pdrh::node_fix_index(j.guard, i, "t") << endl;
                        if(i < path.size() - 1)
                        {
                            for (auto reset_it = j.reset.cbegin(); reset_it != j.reset.cend(); reset_it++)
                            {
                                s << "(= " << reset_it->first << "_" << i + 1 << "_0 " <<
                                  pdrh::node_fix_index(reset_it->second, i, "t") << ")";
                            }
                        }
                    }
                }
            }
        }
        s << ")" << endl;
        // defining the last jump
        s << "(and ";
        for(pdrh::mode::jump j : path.at(depth)->jumps)
        {
            if(j.next_id == path.at(depth+1)->id)
            {
                pdrh::node* timed_node_neg = ap::get_time_node_neg(j.guard);
                if (!timed_node_neg)
                {
                    // checking if there is a not in front of the guard predicate because dReal does not work nicely
                    // with double negation
                    s << "(= local_time_" << depth << "_t " << pdrh::node_fix_index(path.at(depth)->time.second, depth, "0") <<
                      ")" << endl;
                    if(j.guard->value == "not")
                    {
                        /*
                        pdrh::node *guard_without_negation = new pdrh::node();
                        pdrh::copy_tree(guard_without_negation, j.guard->operands.front());
                        s << "(forall_t " << path.at(depth)->id << " [0 time_" << depth << "] (" <<
                        pdrh::node_fix_index(guard_without_negation, depth, "t") << "))";
                        delete guard_without_negation;
                        */
                        s << "(forall_t " << path.at(depth)->id << " [0 time_" << depth << "] (" <<
                          pdrh::node_fix_index(j.guard->operands.front(), depth, "t") << "))";
                    }
                        // transforming the negation of disjunction into the conjunction of negations
                    else if(j.guard->value == "or")
                    {
                        for(pdrh::node* n : j.guard->operands)
                        {
                            s << "(forall_t " << path.at(depth)->id << " [0 time_" << depth << "] (not " <<
                              pdrh::node_fix_index(n, depth, "t") << "))";
                        }
                    }
                    else
                    {
                        s << "(forall_t " << path.at(depth)->id << " [0 time_" << depth << "] (not " <<
                          pdrh::node_fix_index(j.guard, depth, "t") << "))";
                    }
                }
                else
                {
                    s << pdrh::node_fix_index(timed_node_neg, depth, "t");
                    delete timed_node_neg;
                }
            }
        }
        s << ")))" << endl;
        // asserting the time point for the last mode
        // final statements
        s << "(check-sat)" << endl;
        s << "(exit)" << endl;
        return s.str();
    }
}


