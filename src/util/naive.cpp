//
// Created by fedor on 29/11/18.
//

#include "naive.h"
#include "fstream"

using namespace std;
using namespace pdrh;

/**
 * Solve an IVP using the first term of Taylor series. This method performs a deterministic evaluation.
 *
 * @param odes - ODE system.
 * @param init - initial value vector.
 * @param param - vector of parameter values.
 * @param time - time limit for solving the IVP.
 * @param step - integration step.
 * @return solution of the IVP.
 */
std::map<std::string, double> naive::solve_ivp(std::map<std::string, pdrh::node *> odes,
                                               std::map<std::string, double> init, double time, double dt)
{
    // if step is greater than time, then step becomes time
    if(dt > time) dt = time;
    double t = 0;
    // integrating over time
    while(t < time)
    {
        // reducing integration step to meet the integration limit
        if(time - t < dt) dt = time - t;
        // iterating through all ODEs and
        // obtaining a new initial value for the next iteration
        for(auto it = odes.begin(); it != odes.end(); it++)
            init[it->first] += node_to_double(it->second, init)*dt;
        t += dt;
    }
    return init;
}


/**
 * Solve an IVP using the first term of Taylor series and record the entire trajectory up to
 * the specified time bound.
 *
 * @param odes - ODE system.
 * @param init - initial value vector.
 * @param param - vector of parameter values.
 * @param time - time limit for solving the IVP.
 * @param step - integration step.
 * @return trajectories for the given IVP.
 */
std::vector<std::map<std::string, double>> naive::trajectory(std::map<std::string, pdrh::node *> odes,
                                                                std::map<std::string, double> init,
                                                                    double time, double dt)
{
//    // converting init into double
//    map<string, double> init_map;
//    for(auto it = init.begin(); it != init.end(); it++) init_map[it->first] = node_to_double(it->second);
    // if step is greater than time, then step becomes time
    if(dt > time) dt = time;
    // integration time
    double t = 0;
    // the resulting trajectory
    vector<map<string, double>> traj;
    // adding simulation time as one of the values
    init[".time"] = t;
    // pushing the initial state
    traj.push_back(init);
    // integrating over time until the time bound or the guard is true
    while(t < time)
    {
        // reducing integration step to meet the integration limit
        if(time - t < dt) break;
        // solving the ODE system
        map<string, double> sol = solve_ivp(odes, init, dt, dt);
        // increasing integration time
        t += dt;
        // increasing the value of integration time in the result
        sol[".time"] = t;
        // increasing the value of global time counter
        sol[".global_time"] += dt;
        // adding the solution into trajectory
        traj.push_back(sol);
        // updating the initial condition for the next iteration
        init = sol;
    }
    return traj;
}

/**
 *
 * @param modes
 * @param init
 * @param depth - exact depth of simulation
 * @param num_points - number of points used for discretisation in IVP solving
 * @param filename - path to the output file
 * @return
 */
void naive::simulate(std::vector<pdrh::mode> modes, std::vector<pdrh::state> init, std::vector<pdrh::state> goal, bool verify,
                        size_t min_depth, size_t max_depth, size_t max_paths, size_t num_points, std::ostream& os)
{
    // the main path queue
    vector<vector<map<string, double>>> paths;
    // parsing the initial states
    for(state st : init)
    {
        map<string, double> init_map = init_to_map(st);
        // setting setting the step, time and mode values
        int init_mode_id = (int) init_map[".mode"];
        init_map[".step"] = 0;
        init_map[".time"] = 0;
        init_map[".global_time"] = 0;
        // setting the temporary set of paths
        paths.push_back({init_map});
    }
    // current path count
    size_t path_count = 0;
    // iterating through all the paths
    while(paths.size() > 0)
    {
        // popping the front of the vector
        vector<map<string, double>> path = paths.front();
        paths.erase(paths.begin());
        // getting the current initial value in the path
        map<string, double> init_map = path.back();
        path.erase(path.end());
        // getting current mode
        mode cur_mode;
        for(mode m : modes)
            if(m.id == (int) init_map[".mode"])
            {
                cur_mode = m;
                break;
            }
        // getting the trajectory up to the time bound
        double dt = node_to_double(cur_mode.time.second) / num_points;
        vector<map<string, double>> traj = trajectory(cur_mode.odes, init_map, node_to_double(cur_mode.time.second), dt);
        // checking if the maximum depth for the path has been reached
        // if the maximum depth is reached; in simulation mode
        // the lower bound is ignored
        if(traj.back()[".step"] >= max_depth && !verify)
        {
            path.insert(path.end(), traj.begin(), traj.end());
            // separating the paths
            if(path_count > 0) os << ",";
            // outputting a trajectory
            output_traj(path, os);
            path_count++;
        }
        // flag for checking if at least one jump condition has been satisfied
        bool jump_enabled = false;
        // iterating through the simulated trajectory
        for(size_t i = 0; i < traj.size(); i++)
        {
            map<string, double> sol = traj[i];
            // the verify flag is up, hence we need to check the invariants and the goals
            if(verify)
            {
                // checking invariants here
                for(node* invt : cur_mode.invts)
                {
                    // if an invariant does not hold then we break,
                    // report the witness and output the trajectory
                    if(!node_to_boolean(invt, sol))
                    {
                        // always output the outcome
                        cout << "unsat" << endl;
                        // report more info
                        cout << "invariant \"" << node_to_string_infix(invt) << "\" has been violated at:" << endl;
                        for(auto it = sol.begin(); it != sol.end(); it++) cout << it->first << " : " << it->second << endl;
                        // adding the computed trajectory to the end of the current path
                        path.insert(path.end(), traj.begin(), traj.begin() + i + 1);
                        // outputting the unsatisfying trajectory
                        output_traj(path, os);
                        return;
                    }
                }
                // checking goal conditions for the paths which length is within the required bounds
                if(sol[".step"] >= min_depth && sol[".step"] <= max_depth)
                {
                    // checking goal conditions here
                    for(state st : goal)
                    {
                        // if a goal is satisfied we break,
                        // report the witness and output the trajectory
                        if(st.id == (int) sol[".mode"] && node_to_boolean(st.prop, sol))
                        {
                            // always output the outcome
                            cout << "sat" << endl;
                            // report more info
                            cout << "goal \"" << node_to_string_infix(st.prop) << "\" has been reached at:" << endl;
                            for(auto it = sol.begin(); it != sol.end(); it++) cout << it->first << " : " << it->second << endl;
                            // adding the computed trajectory to the end of the current path
                            path.insert(path.end(), traj.begin(), traj.begin() + i + 1);
                            // outputting the unsatisfying trajectory
                            output_traj(path, os);
                            return;
                        }
                    }
                }
            }
            // checking the jumps guards
            for(mode::jump j : cur_mode.jumps)
            {
                // jump condition is satisfied
                if(node_to_boolean(j.guard, sol))
                {
                    // setting the jump flag to true
                    jump_enabled = true;
                    // adding the computed trajectory to the end of the current path
                    path.insert(path.end(), traj.begin(), traj.begin() + i + 1);
                    // reassigning the value for all the variables without any specific resets
                    init_map = sol;
                    // applying the specified resets
                    for(auto it = init_map.begin(); it != init_map.end(); it++)
                        // the variable is not reset; its current value is carried to the next mode
                        if(j.reset.find(it->first) != j.reset.end()) init_map[it->first] = node_to_double(j.reset[it->first], sol);
                    // resetting the auxiliary variables
                    init_map[".step"]++;
                    init_map[".time"] = 0;
                    init_map[".mode"] = j.next_id;
                    // copying the existing path here
                    vector<map<string, double>> new_path = path;
                    // pushing the initial condition to the next mode
                    new_path.push_back(init_map);
                    // pushing the path into the set of all paths if their total number is below the defined limit
                    // and the length of the newly obtained path is smaller than the provided maximum depth
                    if(paths.size() <= max_paths && init_map[".step"] <= max_depth) paths.push_back(new_path);
                    // we assume that as soon as jump takes place we stop considering this trajectory
                    // despite the fact that the corresponding jump can be satisfied multiple times
                }
            }
        }
        // printing out a message saying that no jumps can be made from the current mode
        if(!jump_enabled)
        {
            cout << "no jumps can be made from the current mode" << endl;
            // outputting the witness
            for(auto it = init_map.begin(); it != init_map.end(); it++) cout << it->first << " : " << it->second << endl;
            // outputting the incomplete path
            path.insert(path.end(), traj.begin(), traj.end());
            // outputting the unsatisfying trajectory
            output_traj(path, os);
        }

    }
    if(verify)
    {
        // if we made it here in "verification" mode, then neither of the goal states can be reached
        cout << "unsat" << endl;
        // report more info
        cout << "goals could not be reached" << endl;
    }
}


















