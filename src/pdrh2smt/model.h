//
// Created by fedor on 03/02/17.
//

#ifndef PROBREACH_MODEL_H
#define PROBREACH_MODEL_H

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
    vector<pair<int, node>> inits;

    // list of goal states
    vector<pair<int, node>> goals;

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

    // returns true if the variable exists and false otherwise
    bool var_exists(string);

    // computes and returns the shortest path between one of the initial modes and one of the goal modes.
    // The returned vector is empty if such path does not exist
    vector<int> find_shortest_path();

    // computes returns all paths of specified length between the initial and the goal states.
    // The returned vector is empty if such paths do not exist
    vector<vector<int>> find_all_paths_of_length(int);


    // overriding operators
    friend std::ostream& operator<<(std::ostream&, model&);

    // returns list of variables defined for the model
    map<string, pair<node, node>> get_var_map();

    // returns bounds for the specified variable.
    // Returns a pair of empty nodes if the variable does not exist.
    pair<node, node> get_var_bounds(string);

    // returns time bounds
    pair<node, node> get_time_bounds();

    // returns a list of nodes
    vector<mode> get_modes();

    // returns mode with the specified id. Throws an exception if the corresponding mode
    // has not been defined
    mode get_mode(int);

    // returns list of initial states
    vector<pair<int, node>> get_inits();

    // returns disjunction of the predicates of the initial state for the specified id
    node get_init(int);

    // returns list of goal states
    vector<pair<int, node>> get_goals();

    // returns disjunction of the predicates of the goal state for the specified id
    node get_goal(int);

};

extern model parse_pdrh(string);

#endif //PROBREACH_MODEL_H
