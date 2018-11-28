//
// Created by fedor on 28/11/18.
//

#ifndef PROBREACH_NODE_H
#define PROBREACH_NODE_H

#include <iostream>
#include <vector>
#include <map>

namespace pdrh
{
    // node of the tree of mathematical expression
    struct node
    {
        // either a name of operation or a value of the operand (const or identifier)
        std::string value;
        // vector is empty if the node is terminal and non-empty if the node is operation node
        std::vector<node*> operands;

        inline node(const node &rhs)
                : value(rhs.value), operands(rhs.operands)
        {
        }

        inline node(const std::string value, const std::vector<node*> operands)
                : value(value), operands(operands)
        {
        }

        inline node(const std::string value)
                : value(value)
        {
        }

        inline node()
        {
        }

        inline node &operator =(const node &rhs)
        {
            value = rhs.value;
            operands = rhs.operands;
            return *this;
        }

        // implement the correct comparison of two vectors
        inline bool operator ==(const node &rhs)
        {
            return (value == rhs.value) && (operands == rhs.operands);
        }

        inline bool operator !=(const node &rhs)
        {
            return !(*this == rhs);
        }

    };

    node* push_terminal_node(std::string);
    node* push_terminal_node(double);
    node* push_operation_node(std::string, std::vector<node*>);

    node* copy_node(node*);
    void copy_tree(node*&, node*);
    void delete_node(node*);

    double node_to_double(pdrh::node*);
    double node_to_double(pdrh::node*, std::map<std::string, double>);

    std::string node_to_string_prefix(node*);
    std::string node_to_string_infix(node*);

    std::string node_fix_index(node*, int, std::string);
    bool is_node_empty(node*);
}

#endif //PROBREACH_NODE_H
