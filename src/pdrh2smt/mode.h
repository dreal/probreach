//
// Created by fedor on 03/02/17.
//

#ifndef PROBREACH_MODE_H
#define PROBREACH_MODE_H


#include <map>
#include "node.h"
#include "jump.h"

class mode
{

protected:

    // id of the mode
    int id;

    // list of mode invariants
    vector<node> invts;

    // list of jumps
    vector<jump> jumps;

    // list of ODEs
    map<string, node> ode_map;

    // list of variables for which the ODEs were defined
    map<string, pair<node*, node*>> var_map;

public:

    // default constructor
    mode();

    // creates a mode given a mode id, a list of invariants,
    // a list of jumps and a list of odes
    mode(int, vector<node>, vector<jump>, map<string, node>);

    // returns id of the mode
    int get_id();

    // returns a list of invariants
    vector<node> get_invariants();

    // returns a list of jumps
    vector<jump> get_jumps();

    // returns a list of odes
    map<string, node> get_odes();

    // returns a list of variables
    map<string, pair<node*, node*>> get_vars();

};


#endif //PROBREACH_MODE_H
