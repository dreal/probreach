//
// Created by fedor on 01/03/17.
//

#include <sstream>
#include "isat_generator.h"

// Generates declaration for the variables
string generate_var_declaration(model m, int depth)
{
    stringstream s;
    s << "DECL" << endl;
    // defining boolean variables
    s << "boole flow;" << endl;
    for(mode md : m.get_modes())
    {
        s << "boole mode_" << md.get_id() << ";" << endl;
    }
    // defining variables
    map<string, pair<node, node>> vars = m.get_var_map();
    for(auto it = vars.begin(); it != vars.end(); it++)
    {
        s << "float [" << it->second.first.to_infix() << ", " << it->second.second.to_infix() << "] " << it->first << ";" << endl;
    }
    // defining time and delta_time
    pair<node, node> time_bounds = m.get_time_bounds();
//    // converting int depth to string
//    stringstream tmp;
//    tmp << depth;
//    string depth_str = tmp.str();
//    // defining new bounds according to the depth
//    pair<node, node> new_time_bounds = make_pair(node("*", vector<node>{node(depth_str), time_bounds.first}),
//                                                 node("*", vector<node>{node(depth_str), time_bounds.second}));
    s << "float [" << time_bounds.first.to_infix() << ", " << time_bounds.second.to_infix() << "] time;" << endl;
    s << "float [" << time_bounds.first.to_infix() << ", " << time_bounds.second.to_infix() << "] delta_time;" << endl;
    return s.str();
}

// Generates initial condition of the model
string generate_init(model m)
{
    stringstream s;
    s << "INIT" << endl;
    s << "time=0;" << endl;
    s << "flow;" << endl;
    s << "(" << endl;
    vector<pair<int, node>> inits = m.get_inits();
    for(unsigned long i = 0; i < inits.size(); i++)
    {
        pair<int, node> init = inits.at(i);
        // setting the discrete state
        s << "((mode_" << init.first << ")";
        for(mode md : m.get_modes())
        {
            if(md.get_id() != init.first)
            {
                s << "and(!mode_" << md.get_id() << ")";
            }
        }
        // generating assignment for continuous variables
        s << "and(" << init.second.to_infix() << "))" << endl;
        if(i < inits.size() - 1)
        {
            s << "or" << endl;
        }
    }
    s << ");" << endl;
    return s.str();
}

// Generates some code which required for the model
string generate_required_code(model m)
{
    stringstream s;
    // generating time transition
    s << "time' = time + delta_time;" << endl;
    // flow is followed by a jump
    s << "flow -> !flow';" << endl;
    // flow takes time
    s << "flow -> delta_time > 0;" << endl;
    // no mode changing inside the flow
    s << "flow -> ";
    vector<mode> modes = m.get_modes();
    for(unsigned long i = 0; i < modes.size(); i++)
    {
        s << "(mode_" << modes.at(i).get_id() << " and mode_" << modes.at(i).get_id() << "')";
        if(i < modes.size() - 1)
        {
            s << " or ";
        }
    }
    s << ";" << endl;
    // jump takes no time
    s << "!flow -> delta_time = 0;" << endl;
    // jump is followed by a flow
    s << "!flow -> flow';" << endl;
    return s.str();
}

// Generates jump
string generate_jump(jump j)
{
    stringstream s;
    // setting guard, discrete state and assignment for continuous variables in the next mode
    s << "(";
    s << "(" << j.get_guard().to_infix() << ") and (mode_" << j.get_id() << "')";
    map<string, node> reset = j.get_reset_map();
    for(auto it = reset.begin(); it != reset.end(); it++)
    {
        s << " and (" << it->first << "' = " << it->second.to_infix() << ")";
    }
    s << ")" << endl;
    return s.str();
}

// Generates ODEs, invariants and jumps
string generate_mode(mode md)
{
    stringstream s;
    // generating odes
    map<string, node> odes = md.get_odes();
    for(auto it = odes.begin(); it != odes.end(); it++)
    {
        s << "flow and mode_" << md.get_id() << " -> (d." << it->first << " / d.time = " << it->second.to_infix() << ");" << endl;
    }
    // generating invariants
    for(node n : md.get_invariants())
    {
        s << n.to_infix("(time)");
    }
    //generating jumps
    vector<jump> jumps = md.get_jumps();
    if(!jumps.empty())
    {
        s << "!flow and mode_" << md.get_id() << " -> " << endl;
        s << "(" << endl;
        for(unsigned long i = 0; i < jumps.size(); i++)
        {
            s << generate_jump(jumps.at(i));
            if(i < jumps.size() - 1)
            {
                s << "or" << endl;
            }
        }
        s << ");" << endl;
    }
    return s.str();
}


// Generates flows, jumps and invariants for the model
string generate_trans(model m)
{
    stringstream s;
    s << "TRANS" << endl;
    s << generate_required_code(m);
    for(mode md : m.get_modes())
    {
        s << generate_mode(md);
    }
    return s.str();
}

// Generates the target for the model
string generate_target(model m)
{
    stringstream s;
    s << "TARGET" << endl;
    s << "(" << endl;
    vector<pair<int, node>> goals = m.get_goals();
    for(unsigned long i = 0; i < goals.size(); i++)
    {
        pair<int, node> goal = goals.at(i);
        // setting the discrete state
        s << "((mode_" << goal.first << ")";
        for(mode md : m.get_modes())
        {
            if(md.get_id() != goal.first)
            {
                s << "and(!mode_" << md.get_id() << ")";
            }
        }
        // generating assignment for continuous variables
        s << "and(" << goal.second.to_infix() << "))" << endl;
        if(i < goals.size() - 1)
        {
            s << "or" << endl;
        }
    }
    s << ");" << endl;
    return s.str();
}

string isat_generator::generate_isat_model(model m, int depth)
{
    stringstream s;
    // generating var declaration
    s << generate_var_declaration(m, depth);
    // generating initial condition
    s << generate_init(m);
    // generating transitions
    s << generate_trans(m);
    // generating target condition
    s << generate_target(m);
    return s.str();
}

string isat_generator::generate_isat_model(model m)
{
    return isat_generator::generate_isat_model(m, 1);
}