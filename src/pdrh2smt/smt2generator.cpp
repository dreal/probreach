//
// Created by fedor on 08/02/17.
//

#include "smt2generator.h"
#include <sstream>
#include <algorithm>

string smt2generator::generate_reachability_formula(model m)
{
    stringstream s;
    vector<int> path = m.find_shortest_path();
    // checking if the shortest path exists
    if(path.size() == 0)
    {
        return s.str();
    }
    // generating smt2 formula
    // setting logic
    s << "(set-logic QF_NRA_ODE)" << endl;
    // declaring variables and defining bounds
    map<string, pair<node, node>> vars = m.get_var_map();
    for(auto it = vars.begin(); it != vars.cend(); it++)
    {
        s << "(declare-fun " << it->first << " () Real)" << endl;
        for(int i = 0; i < path.size(); i++)
        {
            s << "(declare-fun " << it->first << "_" << i << "_0 () Real)" << endl;
            s << "(declare-fun " << it->first << "_" << i << "_t () Real)" << endl;
            if(it->second.first.get_value() != "-infty")
            {
                s << "(assert (>= " << it->first << "_" << i << "_0 " << it->second.first.to_prefix() << "))" << endl;
                s << "(assert (>= " << it->first << "_" << i << "_t " << it->second.first.to_prefix() << "))" << endl;
            }
            if(it->second.second.get_value() != "infty")
            {
                s << "(assert (<= " << it->first << "_" << i << "_0 " << it->second.second.to_prefix() << "))" << endl;
                s << "(assert (<= " << it->first << "_" << i << "_t " << it->second.second.to_prefix() << "))" << endl;
            }
        }
    }
    // declaring time
    for(int i = 0; i < path.size(); i++)
    {
        s << "(declare-fun time_" << i << " () Real)" << endl;
        s << "(assert (>= time_" << i << " " << m.get_time_bounds().first.to_prefix() << "))" << endl;
        s << "(assert (<= time_" << i << " " << m.get_time_bounds().second.to_prefix() << "))" << endl;
    }
    // defining odes
//    for(auto path_it = path.begin(); path_it != path.end(); path_it++)
//    {
//        if(find(path.begin(), path_it, *path_it) == path_it)
//        {
//            s << "(define-ode flow_" << path_it << " (";
//            for(auto ode_it = (*path_it)->odes.cbegin(); ode_it != (*path_it)->odes.cend(); ode_it++)
//            {
//                s << "(= d/dt[" << ode_it->first << "] " << pdrh::node_to_string_prefix(ode_it->second) << ")";
//            }
//            s << "))" << endl;
//        }
//    }

    //node init = m.get_init(path.front());
    //node goal = m.get_goal(path.back());




//    // defining the reachability formula
//    s << "(assert (and " << endl;
//    // defining initial states
//    s << "(or ";
//    for(pdrh::state st : pdrh::init)
//    {
//        s << "(" << pdrh::node_fix_index(st.prop, 0, "0") << ")";
//    }
//    s << ")" << endl;
//    // defining boxes bounds
//    for(box b : boxes)
//    {
//        map<string, capd::interval> m = b.get_map();
//        for(auto it = m.cbegin(); it != m.cend(); it++)
//        {
//            s << "(>= " << it->first << "_0_0 " << it->second.leftBound() << ")" << endl;
//            s << "(<= " << it->first << "_0_0 " << it->second.rightBound() << ")" << endl;
//        }
//    }
//    // defining trajectory
//    int step = 0;
//    for(pdrh::mode* m : path)
//    {
//        // defining integrals
//        s << "(= [";
//        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
//        {
//            s << ode_it->first << "_" << step << "_t ";
//        }
//        s << "] (integral 0.0 time_" << step << " [";
//        for(auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++)
//        {
//            s << ode_it->first << "_" << step << "_0 ";
//        }
//        s << "] flow_" << m->id << "))" << endl;
//        // defining invariants
//        for(pdrh::node* invt : m->invts)
//        {
//            s << "(forall_t " << m->id << " [0.0 time_" << step << "] " << pdrh::node_fix_index(invt, step, "t") << ")" << endl;
//        }
//        // checking the current depth
//        if(step < path.size() - 1)
//        {
//            // defining jumps
//            for (pdrh::mode::jump j : m->jumps)
//            {
//                // only the jumps to the next mode in the path
//                if(j.next_id == path.at(step+1)->id)
//                {
//                    s << pdrh::node_fix_index(j.guard, step, "t") << endl;
//                    for (auto reset_it = j.reset.cbegin(); reset_it != j.reset.cend(); reset_it++)
//                    {
//                        s << "(= " << reset_it->first << "_" << step + 1 << "_0 " <<
//                        pdrh::node_fix_index(reset_it->second, step, "t") << ")";
//                    }
//                }
//            }
//        }
//        step++;
//    }
//    // defining goal
//    s << "(or ";
//    for(pdrh::state st : pdrh::goal)
//    {
//        s << "(" << pdrh::node_fix_index(st.prop, path.size() - 1, "t") << ")";
//    }
//    s << ")))" << endl;
//    // final statements
//    s << "(check-sat)" << endl;
//    s << "(exit)" << endl;

    return s.str();
}