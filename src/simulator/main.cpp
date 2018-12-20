//
// Created by fedor on 13/12/18.
//

#include <iostream>
#include <cstring>
#include <sstream>
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

// the minimum depth of each path
size_t min_depth = 0;
// the maximum depth of each path
size_t max_depth = 0;
// the maximum number of paths
size_t max_paths = 1;
// number of point used in IVP solving
size_t num_points = 1;
// path to the input file
string in_file = "";
// path to the output file
string out_file = "output.json";

// printing help message
void print_help()
{
    cout << "Usage:" << endl;
    cout << endl;
    cout << "	simulate <options> <file.pdrh/file.drh> <solver-options>" << endl;
    cout << endl;
    cout << "options:" << endl;
    cout << "-h - displays help message" << endl;
    cout << "-v - displays the tool version" << endl;
    cout << "-l - maximum depth of every simulation path (default = " << min_depth << ")" << endl;
    cout << "-u - maximum depth of every simulation path (default = " << max_depth << ")" << endl;
    cout << "-p - maximum number of simulation paths (default = " << max_paths << ")" << endl;
    cout << "-n - number of points used in IVP solving (default = " << num_points << ")" << endl;
    cout << "-o - full path to the output file (default = " << out_file << ")" << endl;
}

// parsing command line options
void parse_cmd(int argc, char* argv[])
{
    //parsing ProbReach options
    for(int i = 1; i < argc; i++)
    {
        // filename
        if(string(argv[i]).substr(string(argv[i]).find_last_of('.') + 1) == "pdrh" ||
                string(argv[i]).substr(string(argv[i]).find_last_of('.') + 1) == "drh")
        {
            in_file = argv[i];
        }
        // help
        if(strcmp(argv[i], "-h") == 0)
        {
            print_help();
            exit(EXIT_SUCCESS);
        }
        // minimum path length
        else if ((strcmp(argv[i], "-l") == 0))
        {
            i++;
            istringstream is(argv[i]);
            is >> min_depth;
            if (min_depth < 0)
            {
                cerr << "-l must be positive and not larger than -u";
                exit(EXIT_FAILURE);
            }
        }
        // maximum path length
        else if ((strcmp(argv[i], "-u") == 0))
        {
            i++;
            istringstream is(argv[i]);
            is >> max_depth;
            if (max_depth < 0)
            {
                cerr << "-u must be positive and not smaller than -l";
                exit(EXIT_FAILURE);
            }
        }
        // maximum number of paths
        else if ((strcmp(argv[i], "-p") == 0))
        {
            i++;
            istringstream is(argv[i]);
            is >> max_paths;
            if (max_paths < 0)
            {
                cerr << "-p must be positive";
                exit(EXIT_FAILURE);
            }
        }
        // maximum number of points
        else if ((strcmp(argv[i], "-n") == 0))
        {
            i++;
            istringstream is(argv[i]);
            is >> num_points;
            if (num_points < 0)
            {
                cerr << "-n must be positive";
                exit(EXIT_FAILURE);
            }
        }
        // maximum number of points
        else if ((strcmp(argv[i], "-o") == 0))
        {
            i++;
            istringstream is(argv[i]);
            is >> out_file;
        }
    }
    // checking if the input file is specified
    if(in_file == "")
    {
        cerr << "Input file has not been specified" << endl;
        exit(EXIT_FAILURE);
    }
}


int main(int argc, char* argv[])
{
    parse_cmd(argc, argv);
    // opening pdrh file
    FILE *pdrhfile = fopen(in_file.c_str(), "r");
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
    // creating the output file
    ofstream ofs;
    ofs.open(out_file);
    ofs << "{ \"trajectories\" : [" << endl;

    // simulating the model
    simulate(modes, init, goal, false, min_depth, max_depth, max_paths, num_points, ofs);

    // finalising the output file here
    ofs << "]}" << endl;
    ofs.close();

    return 0;
}

