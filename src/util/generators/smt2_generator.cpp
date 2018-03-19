//
// Created by fedor on 06/11/17.
//

#include "smt2_generator.h"

using namespace std;
using namespace capd;
using namespace pdrh;

std::string smt2_generator::generate_flow_invt_check(mode *m , interval time, box init, vector<box> boxes)
{
    stringstream s;
    s.precision(16);

    // declaring the logic type
    s << "(set-logic QF_NRA_ODE)" << endl;

    // declaring functions and their bounds
    s << "; declaring functions and their bounds" << endl;
    for(auto it = m->flow_map.begin(); it != m->flow_map.end(); it++)
    {
        s << "(declare-fun " << it->first << " () Real)" << endl;
        s << "(declare-fun " << it->first << "_0_0 () Real)" << endl;
        s << "(declare-fun " << it->first << "_0_t () Real)" << endl;
        if(it->second.first->value != "-infty")
        {
            s << "(assert (>= " << it->first << "_0_0 " << node_to_string_prefix(it->second.first) << "))" << endl;
            s << "(assert (>= " << it->first << "_0_t " << node_to_string_prefix(it->second.first) << "))" << endl;
        }
        if(it->second.second->value != "infty")
        {
            s << "(assert (<= " << it->first << "_0_0 " << node_to_string_prefix(it->second.second) << "))" << endl;
            s << "(assert (<= " << it->first << "_0_t " << node_to_string_prefix(it->second.second) << "))" << endl;
        }
    }

    // assigning the values for the provided samples
    s << "; assigning the values of the sample" << endl;
    for(box b : boxes)
    {
        std::map<string, interval> b_map = b.get_map();
        for(auto it = b_map.begin(); it != b_map.end(); it++)
        {
            s << "(assert (>= " << it->first << "_0_0 " << it->second.leftBound() << "))" << endl;
            s << "(assert (>= " << it->first << "_0_t " << it->second.leftBound() << "))" << endl;
            s << "(assert (<= " << it->first << "_0_0 " << it->second.rightBound() << "))" << endl;
            s << "(assert (<= " << it->first << "_0_t " << it->second.rightBound() << "))" << endl;
        }
    }

    // declaring time
    s << "; declaring time variable and integration bounds" << endl;
    s << "(declare-fun time () Real)" << endl;
    s << "(assert (>= time 0.0))" << endl;
    s << "(assert (<= time " << time.rightBound() << "))" << endl;

    // declaring a variable mocking the time variable
    // not needed for the complement formula
    s << "; declaring a variable mocking the time variable" << endl;
    s << "(declare-fun time_mock () Real)" << endl;
    s << "(declare-fun time_mock_0_0 () Real)" << endl;
    s << "(declare-fun time_mock_0_t () Real)" << endl;

    // defining odes
    s << "; defining odes" << endl;
    s << "(define-ode flow_" << m->id << " (";
    for(auto it = m->odes.begin(); it != m->odes.end(); it++)
    {
        s << "(= d/dt[" << it->first << "] " << node_to_string_prefix(it->second) << ")" << endl;
    }

    // declaring an ode for time_mock variable
    // not needed for the complement formula
    s << "(= d/dt[time_mock] 1.0)" << endl;
    s << "))" << endl;

    // defining initial condition
    s << "; defining initial condition" << endl;
    std::map<string, interval> b_map = init.get_map();
    for(auto it = b_map.begin(); it != b_map.end(); it++)
    {
        s << "(assert (and (>= " << it->first << "_0_0 " << it->second.leftBound() << ") " <<
                            "(<= " << it->first << "_0_0 " << it->second.rightBound() << ")))" << endl;
    }

    // defining the integral
    s << "; defining the integral" << endl;
    s << "(assert (= [";
    for(auto it = m->odes.cbegin(); it != m->odes.cend(); it++)
    {
        s << it->first << "_0_t ";
    }
    s << "time_mock_0_t] (integral 0.0 time [";
    for(auto it = m->odes.cbegin(); it != m->odes.cend(); it++)
    {
        s << it->first << "_0_0 ";
    }
    s << "time_mock_0_0] flow_" << m->id << ")))" << endl;

    // defining invariants
    s << "; defining invariants" << endl;
    for(node* invt : m->invts)
    {
        s << "(assert (forall_t " << m->id << " [0.0 time] " << pdrh::node_fix_index(invt, 0, "t") << "))" << endl;
    }

    // defining the goal for the time mock variable
    s << "; defining goal for the time mock variable" << endl;
    s << "(assert (= time_mock_0_0 0.0))" << endl;
    s << "(assert (= time_mock_0_t " << time.rightBound() << "))" << endl;

    s << "(check-sat)" << endl;
    s << "(exit)" << endl;

    return s.str();
}



std::string smt2_generator::generate_flow_invt_check_c(mode *m , interval time, box init, vector<box> boxes)
{
    stringstream s;
    s.precision(16);

    // declaring the logic type
    s << "(set-logic QF_NRA_ODE)" << endl;

    // declaring functions and their bounds
    s << "; declaring functions and their bounds" << endl;
    for(auto it = m->flow_map.begin(); it != m->flow_map.end(); it++)
    {
        s << "(declare-fun " << it->first << " () Real)" << endl;
        s << "(declare-fun " << it->first << "_0_0 () Real)" << endl;
        s << "(declare-fun " << it->first << "_0_t () Real)" << endl;
        if(it->second.first->value != "-infty")
        {
            s << "(assert (>= " << it->first << "_0_0 " << node_to_string_prefix(it->second.first) << "))" << endl;
            s << "(assert (>= " << it->first << "_0_t " << node_to_string_prefix(it->second.first) << "))" << endl;
        }
        if(it->second.second->value != "infty")
        {
            s << "(assert (<= " << it->first << "_0_0 " << node_to_string_prefix(it->second.second) << "))" << endl;
            s << "(assert (<= " << it->first << "_0_t " << node_to_string_prefix(it->second.second) << "))" << endl;
        }
    }

    // assigning the values for the provided samples
    s << "; assigning the values of the sample" << endl;
    for(box b : boxes)
    {
        std::map<string, interval> b_map = b.get_map();
        for(auto it = b_map.begin(); it != b_map.end(); it++)
        {
            s << "(assert (>= " << it->first << "_0_0 " << it->second.leftBound() << "))" << endl;
            s << "(assert (>= " << it->first << "_0_t " << it->second.leftBound() << "))" << endl;
            s << "(assert (<= " << it->first << "_0_0 " << it->second.rightBound() << "))" << endl;
            s << "(assert (<= " << it->first << "_0_t " << it->second.rightBound() << "))" << endl;
        }
    }

    // declaring time
    s << "; declaring time variable and integration bounds" << endl;
    s << "(declare-fun time () Real)" << endl;
    s << "(assert (>= time 0.0))" << endl;
    s << "(assert (<= time " << time.rightBound() << "))" << endl;

    // defining odes
    s << "; defining odes" << endl;
    s << "(define-ode flow_" << m->id << " (";
    for(auto it = m->odes.begin(); it != m->odes.end(); it++)
    {
        s << "(= d/dt[" << it->first << "] " << node_to_string_prefix(it->second) << ")" << endl;
    }
    s << "))" << endl;

    // defining initial condition
    s << "; defining initial condition" << endl;
    std::map<string, interval> b_map = init.get_map();
    for(auto it = b_map.begin(); it != b_map.end(); it++)
    {
        s << "(assert (and (>= " << it->first << "_0_0 " << it->second.leftBound() << ") " <<
                            "(<= " << it->first << "_0_0 " << it->second.rightBound() << ")))" << endl;
    }

    // defining the integral
    s << "; defining the integral" << endl;
    s << "(assert (= [";
    for(auto it = m->odes.cbegin(); it != m->odes.cend(); it++)
    {
        s << it->first << "_0_t ";
    }
    s << "] (integral 0.0 time [";
    for(auto it = m->odes.cbegin(); it != m->odes.cend(); it++)
    {
        s << it->first << "_0_0 ";
    }
    s << "] flow_" << m->id << ")))" << endl;

    // defining invariants negations
    s << "; defining invariants negations" << endl;
    s << "(assert (or" << endl;
    for(node* invt : m->invts)
    {
        s << "(not " << pdrh::node_fix_index(invt, 0, "t") << ")" << endl;
    }
    s << "))" << endl;

    s << "(check-sat)" << endl;
    s << "(exit)" << endl;

    return s.str();
}


std::string smt2_generator::generate_jump_check(mode *m , vector<mode::jump> jumps, box init, vector<box> boxes)
{
    stringstream s;
    s.precision(16);

    // declaring the logic type
    s << "(set-logic QF_NRA_ODE)" << endl;

    // declaring functions and their bounds
    s << "; declaring functions and their bounds" << endl;
    for(auto it = m->flow_map.begin(); it != m->flow_map.end(); it++)
    {
        s << "(declare-fun " << it->first << " () Real)" << endl;
        s << "(declare-fun " << it->first << "_0_0 () Real)" << endl;
        s << "(declare-fun " << it->first << "_0_t () Real)" << endl;
        if(it->second.first->value != "-infty")
        {
            s << "(assert (>= " << it->first << "_0_0 " << node_to_string_prefix(it->second.first) << "))" << endl;
            s << "(assert (>= " << it->first << "_0_t " << node_to_string_prefix(it->second.first) << "))" << endl;
        }
        if(it->second.second->value != "infty")
        {
            s << "(assert (<= " << it->first << "_0_0 " << node_to_string_prefix(it->second.second) << "))" << endl;
            s << "(assert (<= " << it->first << "_0_t " << node_to_string_prefix(it->second.second) << "))" << endl;
        }
    }

    // assigning the values for the provided samples
    s << "; assigning the values of the sample" << endl;
    for(box b : boxes)
    {
        std::map<string, interval> b_map = b.get_map();
        for(auto it = b_map.begin(); it != b_map.end(); it++)
        {
            s << "(assert (>= " << it->first << "_0_0 " << it->second.leftBound() << "))" << endl;
            s << "(assert (>= " << it->first << "_0_t " << it->second.leftBound() << "))" << endl;
            s << "(assert (<= " << it->first << "_0_0 " << it->second.rightBound() << "))" << endl;
            s << "(assert (<= " << it->first << "_0_t " << it->second.rightBound() << "))" << endl;
        }
    }

    // declaring time
    s << "; declaring time variable and integration bounds" << endl;
    s << "(declare-fun time () Real)" << endl;
    s << "(assert (>= time " << pdrh::node_to_string_prefix(m->time.first) << "))" << endl;
    s << "(assert (<= time " << pdrh::node_to_string_prefix(m->time.second) << "))" << endl;

    // declaring a variable mocking the time variable
    // not needed for the complement formula
    s << "; declaring a variable mocking the time variable" << endl;
    s << "(declare-fun time_mock () Real)" << endl;
    s << "(declare-fun time_mock_0_0 () Real)" << endl;
    s << "(declare-fun time_mock_0_t () Real)" << endl;

    // defining odes
    s << "; defining odes" << endl;
    s << "(define-ode flow_" << m->id << " (";
    for(auto it = m->odes.begin(); it != m->odes.end(); it++)
    {
        s << "(= d/dt[" << it->first << "] " << node_to_string_prefix(it->second) << ")" << endl;
    }

    // declaring an ode for time_mock variable
    // not needed for the complement formula
    s << "(= d/dt[time_mock] 1.0)" << endl;
    s << "))" << endl;

    // defining initial condition
    s << "; defining initial condition" << endl;
    std::map<string, interval> b_map = init.get_map();
    for(auto it = b_map.begin(); it != b_map.end(); it++)
    {
        s << "(assert (and (>= " << it->first << "_0_0 " << it->second.leftBound() << ") " <<
          "(<= " << it->first << "_0_0 " << it->second.rightBound() << ")))" << endl;
    }

    // defining the integral
    s << "; defining the integral" << endl;
    s << "(assert (= [";
    for(auto it = m->odes.cbegin(); it != m->odes.cend(); it++)
    {
        s << it->first << "_0_t ";
    }
    s << "time_mock_0_t] (integral 0.0 time [";
    for(auto it = m->odes.cbegin(); it != m->odes.cend(); it++)
    {
        s << it->first << "_0_0 ";
    }
    s << "time_mock_0_0] flow_" << m->id << ")))" << endl;

    // defining jumps
    s << "; defining jumps" << endl;
    s << "(assert (or " << endl;
    for(mode::jump jump : jumps)
    {
//        if(jump.guard->operands.front()->value != "counter" && jump.guard->operands.back()->value != "counter")
//        {
            s << pdrh::node_fix_index(jump.guard, 0, "t") << endl;
//        }
    }
    s << "))" << endl;

    // defining the goal for the time mock variable
    // mock time variable is not used in the check
    s << "; defining goal for the time mock variable" << endl;
    s << "(assert (= time_mock_0_0 0.0))" << endl;
    s << "(assert (>= time_mock_0_t 0.0))" << endl;

    s << "(check-sat)" << endl;
    s << "(exit)" << endl;

    return s.str();
}

