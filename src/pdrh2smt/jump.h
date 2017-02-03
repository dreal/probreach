//
// Created by fedor on 03/02/17.
//

#ifndef PROBREACH_JUMP_H
#define PROBREACH_JUMP_H

#include <map>
#include "node.h"

class jump
{

protected:

    // successor mode id
    int id;
    // condition when the jump is enabled
    node guard;
    // specifies the initial value of each variable in the successor mode
    map<string, node> reset_map;

public:

    // default constructor
    jump();

    // creates a jump given an id of the successor mode, a guard and a reset map
    jump(int, node, map<string, node>);

    // creates a jump given an id of the successor mode and a guard
    jump(int, node);

    // adds a reset predicate for the variable specified in the first argument
    // if it has not been defined before and throw invalid_argument exception otherwise
    void push_reset(string, node);

    // returns id of the successor mode
    int get_id();

    // returns the predicate specifying when the jump is enabled
    node get_guard();

    // returns the reset map
    map<string, node> get_reset_map();

};


#endif //PROBREACH_JUMP_H
