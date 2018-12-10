//
// Created by fedor on 23/01/17.
//

#include <gtest/gtest.h>
#include "node.h"
#include <cmath>
#include <util/naive.h>

using namespace std;
using namespace pdrh;
using namespace naive;

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

    // defining the initial condition
    map<string, double> init;
    init["Sx"] = 0;
    init["Sy"] = 0;
    init["t"] = 0;
    init["v0"] = 20;
    init["g"] = 9.81;
    init["alpha"] = 0.7854;

    // defining the time limit and integration step
    double time = 3;
    double dt = 1e-1;

    // solving the ODEs system
    map<string, double> sol = solve_ivp(odes, init, time, dt);

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
    // defining the initial condition
    map<string, node*> init;
    init["Sx"] = new node("0");
    init["Sy"] = new node("0");
    init["t"] = new node("0");
    init["v0"] = new node("dist_uniform", {new node("18"), new node("22")});
    init["g"] = new node("9.81");
    init["alpha"] = new node("0.7854");
    // defining the time limit and integration step
    double time = 5;
    double dt = 1e-4;
    // defining the guard
//    pdrh::node* guard = new node("and", {new node(">", {new node("t"), new node("1e-6")}),
//                                         new node("=", {new node("Sy"), new node("0")})});
    pdrh::node* guard = new node("<", {new node("Sy"), new node("0")});
    // solving the ODEs system
    vector<map<string, double>> traj = trajectory(odes, init, guard, time, dt);
    // printing out the trajectory
//    for(map<string, double> t : traj)
//    {
//        for(auto it = t.begin(); it != t.end(); it++)
//        {
//            cout << it->first << ": " << it->second << endl;
//        }
//        cout << "-----" << endl;
//    }
    EXPECT_NEAR(traj.back()["Sy"], 0, 1e-3);
//    EXPECT_EQ(traj.size(), ceil(time / dt)+1);
}
