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
    size_t depth = 300;
    size_t max_paths = 1;
    double dt = 1e-2;
    vector<vector<map<string, double>>> trajs;
    // simulating for all the initial states
    for(state st : init)
    {
        // converting init into a map
        map<string, node*> init_map = init_to_map(st);
        simulate(modes, init_map, depth, max_paths, dt, "trajectories.json");
    }

    return 0;
}