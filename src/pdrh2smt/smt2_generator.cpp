//
// Created by fedor on 08/02/17.
//

#include "smt2_generator.h"
#include <sstream>
#include <algorithm>

// private methods

string path_to_string(vector<int> path)
{
    stringstream s;
    for(int i = 0; i < path.size()-1; i++)
    {
        s << path.at(i) << " ";
    }
    s << path.at(path.size()-1);
    return s.str();
}

// Generates "<underscore>path_id<underscore>depth"
string generate_index(unsigned long path_id, unsigned long depth)
{
    stringstream s;
    s << "_" << path_id << "_" << depth;
    return s.str();
}

// Generates "<underscore>path_id<underscore>depth<underscore>0"
string generate_0_index(unsigned long path_id, unsigned long depth)
{
    stringstream s;
    s << generate_index(path_id, depth) << "_0";
    return s.str();
}

// Generates "<underscore>path_id<underscore>depth<underscore>t"
string generate_t_index(unsigned long path_id, unsigned long depth)
{
    stringstream s;
    s << generate_index(path_id, depth) << "_t";
    return s.str();
}

// Generates "var<underscore>path_id<underscore>depth<underscore>0"
string generate_0_var(string var, unsigned long path_id, unsigned long depth)
{
    stringstream s;
    s << var << generate_0_index(path_id, depth);
    return s.str();
}

// Generates "var<underscore>path_id<underscore>depth<underscore>t"
string generate_t_var(string var, unsigned long path_id, unsigned long depth)
{
    stringstream s;
    s << var << generate_t_index(path_id, depth);
    return s.str();
}

// Returns unique elements in the specified vector of vectors
vector<int> get_unique_elements(vector<vector<int>> paths)
{
    // concatenating all paths here
    vector<int> unique_path;
    for(vector<int> path : paths)
    {
        unique_path.insert(unique_path.end(), path.begin(), path.end());
    }
    // sorting the obtained long path
    sort(unique_path.begin(), unique_path.end());
    // leaving only unique elements in the long path
    auto it = unique(unique_path.begin(), unique_path.end());
    unique_path.erase(it, unique_path.end());
    return unique_path;
}

// Returns unique elements in the specified vector
vector<int> get_unique_elements(vector<int> path)
{
    return get_unique_elements(vector<vector<int>>{path});
}

// Returns unique elements in the specified vector of vectors
vector<string> get_unique_elements(vector<vector<string>> paths)
{
    // concatenating all paths here
    vector<string> unique_path;
    for(vector<string> path : paths)
    {
        unique_path.insert(unique_path.end(), path.begin(), path.end());
    }
    // sorting the obtained long path
    sort(unique_path.begin(), unique_path.end());
    // leaving only unique elements in the long path
    auto it = unique(unique_path.begin(), unique_path.end());
    unique_path.erase(it, unique_path.end());
    return unique_path;
}

// Returns unique elements in the specified vector
vector<string> get_unique_elements(vector<string> path)
{
    return get_unique_elements(vector<vector<string>>{path});
}

// Generates variables declaration to be used for defining the odes without repetitions
string generate_var_declaration(model m, vector<vector<int>> paths)
{
    stringstream s;
    map<string, pair<node, node>> vars = m.get_var_map();
    s << "; declaring flow variables" << endl;
    // gettting unique modes appearing in all the paths
    vector<int> unique_modes = get_unique_elements(paths);
    vector<string> vars_list;
    for(int id : unique_modes)
    {
        // getting ode_map for the current mode
        map<string, node> ode_map = m.get_mode(id).get_odes();
        for(auto ode_it = ode_map.begin(); ode_it != ode_map.end(); ode_it++)
        {
            vars_list.push_back(ode_it->first);
        }
    }
    // getting unique variables from the list with repetitions
    vector<string> unique_vars = get_unique_elements(vars_list);

    for(string var : unique_vars)
    {
        s << "(declare-fun " << var << " () Real)" << endl;
    }
    return s.str();
}

// Generates variables declaration to be used for defining the odes without repetitions
string generate_var_declaration(model m, vector<int> path)
{
    return generate_var_declaration(m, vector<vector<int>>{path});
}

// Generates variables declaration to be used for defining the odes for all variables in the model.
string generate_var_declaration(model m)
{
    vector<mode> modes = m.get_modes();
    // generating a path containing ids of all modes
    vector<int> path;
    for(mode md : modes)
    {
        path.push_back(md.get_id());
    }
    return generate_var_declaration(m, path);
}

// Generates flows only for the modes specified in the paths
// without repetitions.
string generate_flows(model m, vector<vector<int>> paths)
{
    stringstream s;
    s << "; defining flows" << endl;
    vector<int> unique_modes = get_unique_elements(paths);
    // defining the flows using the obtained unique path
    for(int id : unique_modes)
    {
        s << "(define-ode flow_" << id << " (";
        map<string, node> ode_map = m.get_mode(id).get_odes();
        for(auto ode_it = ode_map.begin(); ode_it != ode_map.end(); ode_it++)
        {
            s << "(= d/dt[" << ode_it->first << "] " << ode_it->second.to_prefix() << ")";
        }
        s << "))" << endl;
    }
    return s.str();
}

// Generates flows only for the modes specified in the path
// without repetitions
string generate_flows(model m, vector<int> path)
{
    return generate_flows(m, vector<vector<int>>{path});
}

// Generates flows for all modes in the model
string generate_flows(model m)
{
    vector<mode> modes = m.get_modes();
    // generating a path containing ids of all modes
    vector<int> path;
    for(mode md : modes)
    {
        path.push_back(md.get_id());
    }
    return generate_flows(m, vector<vector<int>>{path});
}

// Generates variables declaration and bounds for each path.
// Only the variables specified in the mode flow are specified.
string generate_var_declaration_and_bounds(model m, vector<vector<int>> paths)
{
    stringstream s;
    s << "; declaring path variables and setting bounds for the paths" << endl;
    for(unsigned long path_id = 0; path_id < paths.size(); path_id++)
    {
        vector<int> path = paths.at(path_id);
        s << "; declaring path variables and setting bounds for path " << path_to_string(path) << endl;
        for(unsigned long depth = 0; depth < path.size(); depth++)
        {
            // getting variables from the odes for the mode in the current path at the current depth
            //map<string, node> ode_map = m.get_mode(path.at(depth)).get_odes();
            vector<string> vars = m.get_mode(path.at(depth)).get_vars();
            for(string var : vars)
            {
                // declaring the variable
                s << "(declare-fun " << generate_0_var(var, path_id, depth) << " () Real)" << endl;
                s << "(declare-fun " << generate_t_var(var, path_id, depth) << " () Real)" << endl;
                // getting the variable bounds
                pair<node, node> var_bounds = m.get_var_bounds(var);
                // making sure that the variable's bounds are defined
                if((var_bounds.first.get_value() != "-infty") && (!var_bounds.first.is_empty()))
                {
                    s << "(assert (>= " << generate_0_var(var, path_id, depth) << " " << var_bounds.first.to_prefix() << "))" << endl;
                    s << "(assert (>= " << generate_t_var(var, path_id, depth) << " " << var_bounds.first.to_prefix() << "))" << endl;
                }
                if((var_bounds.second.get_value() != "infty") && (!var_bounds.second.is_empty()))
                {
                    s << "(assert (<= " << generate_0_var(var, path_id, depth) << " " << var_bounds.second.to_prefix() << "))" << endl;
                    s << "(assert (<= " << generate_t_var(var, path_id, depth) << " " << var_bounds.second.to_prefix() << "))" << endl;
                }
            }
        }
    }
    return s.str();
}

// generates time variables declaration and bounds to be used for defining the path
string generate_time_declaration_and_bounds(model m, vector<vector<int>> paths)
{
    stringstream s;
    s << "; declaring time" << endl;
    for(unsigned long path_id = 0; path_id < paths.size(); path_id++)
    {
        vector<int> path = paths.at(path_id);
        s << "; declaring time bounds for path " << path_to_string(path) << endl;
        for(unsigned long depth = 0; depth < path.size(); depth++)
        {
            s << "(declare-fun time" << generate_index(path_id, depth) << " () Real)" << endl;
            s << "(assert (>= time" << generate_index(path_id, depth) << " " << m.get_time_bounds().first.to_prefix() << "))" << endl;
            s << "(assert (<= time" << generate_index(path_id, depth) << " " << m.get_time_bounds().second.to_prefix() << "))" << endl;
        }
    }
    return s.str();
}

string generate_init(model m, vector<int> path, unsigned long path_id)
{
    stringstream s;
    s << "; defining initial state" << endl;
    // generating initial state as one big disjunction
    node init = m.get_init(path.front());
    s << init.to_prefix(generate_0_index(path_id,0)) << endl;
    return s.str();
}

string generate_goal(model m, vector<int> path, unsigned long path_id)
{
    stringstream s;
    s << "; defining goal state" << endl;
    // generating goal state as one big disjunction
    node goal = m.get_goal(path.back());
    s << goal.to_prefix(generate_t_index(path_id,path.size()-1)) << endl;
    return s.str();
}


string generate_integral(mode md, unsigned long path_id, unsigned long depth)
{
    stringstream s;
    s << "; defining integral for mode " << md.get_id() << " at depth " << depth << endl;
    // defining integral
    vector<string> vars = md.get_vars();
    s << "(= [";
    for(string var : vars)
    {
        s << generate_t_var(var, path_id, depth) << " ";
    }
    s << "] (integral 0.0 time" << generate_index(path_id, depth) << " [";
    for(string var : vars)
    {
        s << generate_0_var(var, path_id, depth) << " ";
    }
    s << "] flow_" << md.get_id() << "))" << endl;
    return s.str();
}

string generate_invariants(mode md, unsigned long path_id, unsigned long depth)
{
    stringstream s;
    s << "; defining invariant for mode " << md.get_id() << " at depth " << depth << endl;
    node invts = md.get_invariants_conjunction();
    s << "(forall_t " << md.get_id() << " [0.0 time" << generate_index(path_id, depth) << "] " << invts.to_prefix(generate_t_index(path_id, depth)) << ")" << endl;
    return s.str();
}

string generate_jump(jump j, unsigned long path_id, unsigned long depth)
{
    stringstream s;
    s << "(and " << endl;
    //generating guard
    s << "; guard" << endl;
    s << "(" << j.get_guard().to_prefix(generate_t_index(path_id, depth)) << ")" << endl;
    // generating reset
    s << "; reset" << endl;
    s << "(and ";
    map<string, node> reset_map = j.get_reset_map();
    for(auto it = reset_map.begin(); it != reset_map.end(); it++)
    {
        s << "(= " << generate_0_var(it->first, path_id, depth + 1) << " " << it->second.to_prefix(generate_t_index(path_id, depth)) << ")";
    }
    s << "))";
    return s.str();
}

string generate_jumps(vector<jump> jumps, unsigned long path_id, unsigned long depth)
{
    stringstream s;
    s << "; generating jumps at depth " << depth << endl;
    s << "(or " << endl;
    for(jump j : jumps)
    {
        s << generate_jump(j, path_id, depth) << endl;
    }
    s << ")" << endl;
    return s.str();
}

string generate_path(model m, vector<int> path, unsigned long path_id)
{
    stringstream s;
    s << "; defining path " << path_to_string(path) << endl;
    // generating init
    s << "(and " << endl;
    s << generate_init(m, path, path_id) << endl;
    for(unsigned long depth = 0; depth < path.size(); depth++)
    {
        mode md = m.get_mode(path.at(depth));
        // generating integral
        s << generate_integral(md, path_id, depth) << endl;
        // generating invariants
        if(md.get_invariants().size() > 0)
        {
            s << generate_invariants(md, path_id, depth) << endl;
        }
        // generating jumps
        if(depth < path.size() - 1)
        {
            s << generate_jumps(md.get_jumps(), path_id, depth) << endl;
        }
    }
    // generating goal
    s << generate_goal(m, path, path_id) << endl;
    s << ")" << endl;
    return s.str();
}

string generate_paths(model m, vector<vector<int>> paths)
{
    stringstream s;
    s << "; defining paths " << endl;
    s << "(assert (or " << endl;
    for(unsigned long path_id = 0; path_id < paths.size(); path_id++)
    {
        s << generate_path(m, paths.at(path_id), path_id) << endl;
    }
    s << "))" << endl;
    return s.str();
}

// public methods

string smt2generator::generate_reachability_formula(model m, vector<vector<int>> paths)
{
    stringstream s;
    // checking if the path is empty
    if(paths.size() == 0)
    {
        return s.str();
    }
    // generating smt2 formula
    // setting logic
    s << "(set-logic QF_NRA_ODE)" << endl;
    // declaring ode variables
    s << generate_var_declaration(m, paths) << endl;
    // defining flows
    s << generate_flows(m, paths) << endl;
    // defining variables and bounds
    s << generate_var_declaration_and_bounds(m, paths) << endl;
    // defining time bounds
    s << generate_time_declaration_and_bounds(m, paths) << endl;
    // defining paths
    s << generate_paths(m, paths) << endl;
    // final statements
    s << "(check-sat)" << endl;
    s << "(exit)" << endl;

    return s.str();
}

string smt2generator::generate_reachability_formula(model m, vector<int> path)
{
    return smt2generator::generate_reachability_formula(m, vector<vector<int>>{path});
}

string smt2generator::generate_reachability_formula(model m)
{
    return smt2generator::generate_reachability_formula(m, m.find_shortest_path());
}

string smt2generator::generate_reachability_formula(model m, int depth)
{
    return smt2generator::generate_reachability_formula(m, m.find_all_paths_of_length(depth));
}



