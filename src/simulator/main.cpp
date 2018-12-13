//
// Created by fedor on 13/12/18.
//

#include <iostream>
#include <fstream>
#include "node.h"
#include "model.h"
#include "naive.h"

extern "C"
{
#include "pdrhparser.h"
}

extern "C" int yyparse();
extern "C" FILE *yyin;

using namespace std;
using namespace pdrh;
using namespace naive;



int main(int argc, char* argv[])
{
    // opening pdrh file
    FILE *pdrhfile = fopen(argv[1], "r");
    if (!pdrhfile)
    {
        cerr << "Couldn't open the file: " << endl;
        exit(EXIT_FAILURE);
    }
    // set lex to read from it instead of defaulting to STDIN:
    yyin = pdrhfile;
    // parse through the input until there is no more:
    do
    {
        yyparse();
    }
    while (!feof(yyin));
    // setting other values
    size_t depth = 100;
    size_t max_paths = 10;
    double dt = 1e-1;
    vector<vector<map<string, double>>> trajs;
    // simulating for all the initial states
    for(state st : init)
    {
        // converting init into a map
        map<string, node*> init_map = init_to_map(st);
        vector<vector<map<string, double>>> tmp = simulate(modes, init_map, depth, max_paths, dt);
        trajs.insert(trajs.end(), tmp.begin(), tmp.end());
    }
    // printing out the trajectories and writing them into a file
    ofstream outfile;
    outfile.open ("trajectories.json");
    outfile << "{ \"trajectories\" : [" << endl;
    for(vector<map<string, double>> traj : trajs)
    {
        outfile << "[" << endl;
        // printing out the trajectory
        for(map<string, double> t : traj)
        {
            outfile << "{" << endl;
            for(auto it = t.begin(); it != t.end(); it++)
            {
                outfile << "\"" << it->first << "\" : " << it->second;
                if(it != prev(t.end())) outfile << ",";
                outfile << endl;
//                    cout << it->first << ": " << it->second << endl;
            }
            outfile << "}";
            if(t != traj[traj.size()-1]) outfile << ",";
            outfile << endl;
//                cout << "-----" << endl;
        }
        outfile << "]" << endl;
        if(traj != trajs[trajs.size()-1]) outfile << ",";
        outfile << endl;
    }
    outfile << "]}" << endl;
    outfile.close();


//    // defining the ODEs
//    map<string, node*> odes;
//    odes["Sx"] = new node("*", {new node("v0"), new node("cos", {new node("alpha")})});
//    odes["Sy"] = new node("-", {new node("*", {new node("v0"), new node("cos", {new node("alpha")})}),
//                                new node("*", {new node("g"), new node("t")})});
//    odes["t"] = new node("1");
//    // defining the initial condition
//    map<string, node*> init;
//    init["Sx"] = new node("0");
//    init["Sy"] = new node("0");
//    init["t"] = new node("0");
//    init["v0"] = new node("dist_uniform", {new node("18"), new node("22")});
//    init["g"] = new node("9.81");
//    init["alpha"] = new node("0.7854");
////    // setting the initial condition for the trajectory
////    map<string, double> init_map;
////    for(auto it = init.begin(); it != init.end(); it++) init_map[it->first] = node_to_double(it->second);
//    // defining the jump
//    node* guard = new node("<", {new node("Sy"), new node("0")});
//    map<string, node*> reset;
//    reset["Sy"] = new node("0");
//    reset["t"] = new node("0");
////    reset["v0"] = new node("*", {new node("v0"), new node("0.9")});
//    reset["v0"] = new node("*", {new node("v0"), new node("dist_uniform", {new node("0.9"), new node("1.1")})});
//    mode::jump* j = new mode::jump(1, guard, reset);
//    // creating the mode
//    mode* m = new mode();
//    m->id = 1;
//    // defining the time limit
//    m->time.first = new node("0");
//    m->time.second = new node("5");
//    m->odes = odes;
//    m->jumps = {*j};
//    // setting the initial mode before the simulation
//    init[".mode"] = new node("1");
//    size_t depth = 10;
//    size_t max_paths = 10;
//    double dt = 1e-2;
//    // solving the ODEs system
//    vector<vector<map<string, double>>> trajs = simulate({m}, init, depth, max_paths, dt);
//    // printing out the trajectories and writing them into a file
//    ofstream outfile;
//    outfile.open ("trajectories.json");
//    outfile << "{ \"trajectories\" : [" << endl;
//    for(vector<map<string, double>> traj : trajs)
//    {
//        outfile << "[" << endl;
//        // printing out the trajectory
//        for(map<string, double> t : traj)
//        {
//            outfile << "{" << endl;
//            for(auto it = t.begin(); it != t.end(); it++)
//            {
//                outfile << "\"" << it->first << "\" : " << it->second;
//                if(it != prev(t.end())) outfile << ",";
//                outfile << endl;
//                cout << it->first << ": " << it->second << endl;
//            }
//            outfile << "}";
//            if(t != traj.back()) outfile << ",";
//            outfile << endl;
//            cout << "-----" << endl;
//        }
//        outfile << "]" << endl;
//        if(traj != trajs.back()) outfile << ",";
//        outfile << endl;
//    }
//    outfile << "]}" << endl;
//    outfile.close();

    return 0;
}