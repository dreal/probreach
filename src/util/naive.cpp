//
// Created by fedor on 29/11/18.
//

#include "naive.h"

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
    if(dt > time)
    {
        dt = time;
    }
    double t = 0;
    // integrating over time
    while(t < time)
    {
        // reducing integration step to meet the integration limit
        if(time - t < dt)
        {
            dt = time - t;
        }
        // iterating through all ODEs and
        // constructing solution map
        map<string, double> sol;
        for(auto it = odes.begin(); it != odes.end(); it++)
        {
            sol[it->first] = node_to_double(it->second, init);
        }
        // obtaining a new initial value for the next iteration
        for(auto it = sol.begin(); it != sol.end(); it++)
        {
            init[it->first] += sol[it->first]*dt;
        }
        // increasing integration time
        t += dt;
    }
    return init;
}


/**
 * Solve an IVP using the first term of Taylor series and record the entire trajectory.
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
    return naive::trajectory(odes, init, new node("=", {new node("1"), new node("0")}), time, dt);
}


/**
 * Solve an IVP using the first term of Taylor series and record the entire trajectory up to
 * the specified time bound or until the guard condition is satisfied (whichever comes first).
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
                                                                    pdrh::node * guard, double time, double dt)
{
//    // converting init into double
//    map<string, double> init_map;
//    for(auto it = init.begin(); it != init.end(); it++) init_map[it->first] = node_to_double(it->second);
    // if step is greater than time, then step becomes time
    if(dt > time)
    {
        dt = time;
    }
    // integration time
    double t = 0;
    // the resulting trajectory
    vector<map<string, double>> traj;
    // adding simulation time as one of the values
    init[".time"] = t;
    // pushing the initial state
    traj.push_back(init);
//    // checking if the guard can be satisfied right away
    if(node_to_boolean(guard, init)) return traj;
    // integrating over time until the time bound or the guard is true
    while(t < time)
    {
        // reducing integration step to meet the integration limit
        if(time - t < dt)
        {
            dt = time - t;
        }
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
        // checking if the guard condition is satisfied
        if(node_to_boolean(guard, sol)) break;
        // updating the initial condition for the next iteration
        init = sol;
    }
    return traj;
}

/**
 *
 * @param modes
 * @param init
 * @param depth
 * @param dt
 * @return
 */
std::vector<std::vector<std::map<std::string, double>>> naive::simulate(std::vector<pdrh::mode> modes,
                                                                std::map<std::string, pdrh::node *> init,
                                                                    size_t depth, size_t max_paths, double dt)
{
    // change init from node map into a double map
    map<string, double> init_map;
    for(auto it = init.begin(); it != init.end(); it++) init_map[it->first] = node_to_double(it->second);
    // setting setting the step, time and mode values
    int init_mode_id = (int) init_map[".mode"];
    init_map[".step"] = 0;
    init_map[".time"] = 0;
    init_map[".global_time"] = 0;
    // setting the temporary set of paths
    vector<vector<map<string, double>>> paths = {{ init_map }};
    vector<vector<map<string, double>>> res_paths;
    // iterating through all the paths
    while(paths.size() > 0)
    {
        // popping the front of the vector
        vector<map<string, double>> path = paths.front();
        paths.erase(paths.begin());
        // getting the current initial value in the path
        init_map = path.back();
        path.erase(path.end());
        // getting current mode
        mode cur_mode;
        for(mode m : modes)
            if(m.id == (int) init_map[".mode"])
            {
                cur_mode = m;
                break;
            }
        // getting through all the jumps in the trajectory
        for(mode::jump j : cur_mode.jumps)
        {
            // getting the trajectory up to the jump or until the time bound
            vector<map<string, double>> traj = trajectory(cur_mode.odes, init_map, j.guard, node_to_double(cur_mode.time.second), dt);
            // adding the computed trajectory to the end
            path.insert(path.end(), traj.begin(), traj.end());
            // if the jump condition has not been satisfied, then this is the end of simulation for this path
            if(!node_to_boolean(j.guard, path.back()))
            {
                res_paths.push_back(path);
                break;
            }
            // if the jump occurs then apply the reset
            map<string, double> sol = path.back();
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
            // pushing the initial condition to the next mode
            path.push_back(init_map);
            // checking if the path length has reached the defined limit
            if(init_map[".step"] > depth) res_paths.push_back(path);
                else paths.push_back(path);
        }
    }
    return res_paths;
}




















