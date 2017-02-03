//
// Created by fedor on 03/02/17.
//

#ifndef PROBREACH_MODEL_H
#define PROBREACH_MODEL_H

#include "node.h"
#include "mode.h"
#include <map>

class model
{

protected:

    // time bounds
    pair<node, node> time;

    // list of variables with the bounds
    map<string, pair<node, node>> var_map;

    // list of initial states
    map<int, node> init_map;

    // list of goal states
    map<int, node> goal_map;

    // list of modes
    vector<mode> modes;

public:

    // default constructor
    model();

    // sets the bounds for the time variable if they have not beed set yet and
    // throws invalid_argument exception otherwise
    void set_time(node, node);

    // adds a variable with its bounds to the list argument if has not been declared yet and
    // throws invalid_argument exception otherwise
    void push_var(string, node, node);

    // adds a mode (id, mode) to the list of modes if a mode
    // has not been defined yet and throws invalid_argument exception otherwise
    void push_mode(mode);

    // adds initial state (id, predicate) to the list of initial states and
    // throws invalid_argument exception the mode with the specified id does not exist
    void push_init(int, node);

    // adds goal state (id, predicate) to the list of goal states and
    // throws invalid_argument exception the mode with the specified id does not exist
    void push_goal(int, node);




};


#endif //PROBREACH_MODEL_H
