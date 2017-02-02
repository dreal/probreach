//
// Created by fedor on 02/02/17.
//

#ifndef PROBREACH_NODE_H
#define PROBREACH_NODE_H

#include <iostream>
#include <vector>

using namespace std;

class node {

protected:

    // either a name of operation or a value of the operand (const or identifier)
    string value;

    // vector is empty if the node is terminal and non-empty if the node is operation node
    vector<node> operands;

public:

    // default constructor
    node();

    // constructor creates a terminal node
    node(string);

    // constructor creates an operation node
    node(string, vector<node>);

    // appends node to the list of operands in the current node
    void append(node);

    // appends a list of nodes to the list of operands in the current node
    void append(vector<node>);

    // returns true if the node does not have operands and false otherwise
    bool is_terminal();

    // returns true if the node does not have operands and its value is an empty string
    // and false otherwise
    bool is_empty();

    // returns a string representation of the node in infix notation
    string to_string_infix();

    // returns a string representation of the node in prefix notation
    string to_string_prefix();

    friend std::ostream& operator<<(std::ostream&, const node&);

};


#endif //PROBREACH_NODE_H
