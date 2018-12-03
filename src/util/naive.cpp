//
// Created by fedor on 29/11/18.
//

#include "naive.h"

using namespace std;
using namespace pdrh;

/**
 * Solve an IVP using the first term of Taylor series.
 *
 * @param odes - ODE system.
 * @param init - initial value vector.
 * @param param - vector of parameter values.
 * @param time - time limit for solving the IVP.
 * @param step - integration step.
 * @return solution of the IVP.
 */
std::map<std::string, double> naive::solve_ivp(std::map<std::string, pdrh::node *> odes,
                                               std::map<std::string, double> init,
                                               std::map<std::string, double> param, double time, double dt)
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
            map<string, double> vals;
            vals.insert(param.begin(), param.end());
            vals.insert(init.begin(), init.end());
            sol[it->first] = node_to_double(it->second, vals);
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
                                                                 std::map<std::string, double> param, double time, double dt)
{
    // the resulting trajectory
    vector<map<string, double>> traj;
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
        // solving the ODE system
        map<string, double> sol = solve_ivp(odes, init, param, dt, dt);
        // adding the solution into trajectory
        traj.push_back(sol);
        // updating the initial condition for the next iteration
        init = sol;
        // increasing integration time
        t += dt;
    }
    return traj;
}

























