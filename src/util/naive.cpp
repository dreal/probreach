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
                                                                 std::map<std::string, pdrh::node*> init,
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
                                                                std::map<std::string, pdrh::node *> init,
                                                                    pdrh::node * guard, double time, double dt)
{
    // converting init into double
    map<string, double> init_map;
    for(auto it = init.begin(); it != init.end(); it++) init_map[it->first] = node_to_double(it->second);
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
    init_map[".time"] = t;
    // pushing the initial state
    traj.push_back(init_map);
    // checking if the guard can be satisfied right away
    if(node_to_boolean(guard, init_map)) return traj;
    // integrating over time until the time bound or the guard is true
    while(t < time)
    {
        // reducing integration step to meet the integration limit
        if(time - t < dt)
        {
            dt = time - t;
        }
        // solving the ODE system
        map<string, double> sol = solve_ivp(odes, init_map, dt, dt);
        // increasing integration time
        t += dt;
        // increasing the value of integration time in the result
        sol[".time"] = t;
        // adding the solution into trajectory
        traj.push_back(sol);
        // checking if the guard condition is satisfied
        if(node_zero_crossing(guard, init_map, sol) || node_to_boolean(guard, sol)) break;
        // updating the initial condition for the next iteration
        init_map = sol;
    }
    return traj;
}






















