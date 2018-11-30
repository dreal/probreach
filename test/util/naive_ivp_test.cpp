//
// Created by fedor on 23/01/17.
//

#include <gtest/gtest.h>
#include "node.h"
#include <cmath>
#include <util/naive_ivp.h>

using namespace std;
using namespace pdrh;
using namespace naive_ivp;

/**
 * Testing the solve method of the naive IVP solver.
 */
TEST(naive_ivp_solve, OK)
{
    // defining the ODEs
    map<string, node*> odes;
    odes["Sx"] = new node("*", {new node("v0"), new node("cos", {new node("alpha")})});
    odes["Sy"] = new node("-", {new node("*", {new node("v0"), new node("cos", {new node("alpha")})}),
                                new node("*", {new node("g"), new node("t")})});
    odes["t"] = new node("1");

    // defining the parameters
    map<string, double> param;
    param["v0"] = 20;
    param["g"] = 9.81;
    param["alpha"] = 0.7854;

    // defining the initial condition
    map<string, double> init;
    init["Sx"] = 0;
    init["Sy"] = 0;
    init["t"] = 0;

    // defining the time limit and integration step
    double time = 3;
    double dt = 1e-1;

    // solving the ODEs system
    map<string, double> sol = solve(odes, init, param, time, dt);

    EXPECT_EQ(sol["t"], 3);
}


/**
 * Testing the trajectory method of the naive IVP solver.
 */
TEST(naive_ivp_trajectory, OK)
{
    // defining the ODEs
    map<string, node*> odes;
    odes["Sx"] = new node("*", {new node("v0"), new node("cos", {new node("alpha")})});
    odes["Sy"] = new node("-", {new node("*", {new node("v0"), new node("cos", {new node("alpha")})}),
                                new node("*", {new node("g"), new node("t")})});
    odes["t"] = new node("1");

    // defining the parameters
    map<string, double> param;
    param["v0"] = 20;
    param["g"] = 9.81;
    param["alpha"] = 0.7854;

    // defining the initial condition
    map<string, double> init;
    init["Sx"] = 0;
    init["Sy"] = 0;
    init["t"] = 0;

    // defining the time limit and integration step
    double time = 3;
    double dt = 1e-1;

    // solving the ODEs system
    vector<map<string, double>> traj = trajectory(odes, init, param, time, dt);

    EXPECT_EQ(traj.back()["t"], 3);
    EXPECT_EQ(traj.size(), ceil(time / dt));
}
