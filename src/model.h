//
// Created by fedor on 24/01/16.
//

#ifndef PROBREACH_MODEL_H
#define PROBREACH_MODEL_H

#include <iostream>
#include <vector>
#include <map>
#include <capd/capdlib.h>
#include <capd/intervals/lib.h>
#include <tuple>
#include <box.h>

namespace pdrh
{
    // node of the tree of mathematical expression
    struct node
    {
        // either a name of operation or a value of the operand (const or identifier)
        std::string value;
        // vector is empty if the node is terminal and non-empty if the node is operation node
        std::vector<node*> operands;
    };
    node* push_terminal_node(std::string);
    node* push_operation_node(std::string, std::vector<node*>);
    std::string node_to_string_prefix(node*);
    std::string node_to_string_infix(node*);
    // the second argument is a step
    std::string node_fix_index(node*, int, std::string);
    enum type {HA, PHA, NHA, NPHA, PSY};
    extern type model_type;

    extern capd::interval time;
    extern std::map<std::string, std::tuple<std::string, capd::interval, double>> rv_map;
    extern std::map<std::string, std::string> rv_type_map;
    extern std::map<std::string, std::map<capd::interval, capd::interval>> dd_map;
    extern std::map<std::string, capd::interval> var_map;
    extern std::map<std::string, capd::interval> par_map;
    extern std::map<std::string, capd::interval> syn_map;
    // mode struct
    struct mode
    {
        int id;
        std::vector<pdrh::node*> invts;
        // jump struct
        struct jump
        {
            pdrh::node* guard;
            int next_id;
            std::map<std::string, pdrh::node*> reset;
        };
        std::vector<jump> jumps;
        std::map<std::string, capd::interval> flow_map;
        std::map<std::string, pdrh::node*> odes;
    };
    extern std::vector<mode> modes;
    // state struct
    struct state
    {
        int id;
        pdrh::node* prop;
    };
    extern std::vector<state> init;
    extern std::vector<state> goal;

    void push_var(std::string, capd::interval);
    void push_dd(std::string, std::map<capd::interval, capd::interval>);
    void push_rv(std::string, std::string, capd::interval, double);
    void push_rv_type(std::string, std::string);

    void push_mode(pdrh::mode);
    void push_invt(pdrh::mode&, pdrh::node*);
    // first argument is the address of the mode, second argument is the variable name, third argument is the ode
    void push_ode(pdrh::mode&, std::string, pdrh::node*);
    void push_jump(pdrh::mode&, pdrh::mode::jump);
    // first argument is the address of the jump, second argument is the variable name, third argument is the reset expression
    void push_reset(pdrh::mode&, pdrh::mode::jump&, std::string, pdrh::node*);
    void push_init(std::vector<pdrh::state>);
    void push_goal(std::vector<pdrh::state>);
    void push_psy_goal(int, box);
    void push_psy_c_goal(int, box);
    void push_syn_pair(std::string, capd::interval);
    void push_time_bounds(capd::interval);

    box get_nondet_domain();
    box get_psy_domain();
    std::vector<pdrh::mode*> get_psy_path(std::map<std::string, std::vector<capd::interval>>);

    bool var_exists(std::string);
    pdrh::mode* get_mode(int);

    std::vector<pdrh::mode*> get_init_modes();
    std::vector<pdrh::mode*> get_goal_modes();
    std::vector<pdrh::mode*> get_successors(pdrh::mode*);
    std::vector<pdrh::mode*> get_shortest_path(pdrh::mode*, pdrh::mode*);
    std::vector<std::vector<pdrh::mode*>> get_paths(pdrh::mode*, pdrh::mode*, int);
    std::vector<std::vector<pdrh::mode*>> get_all_paths(int);
    // returns <first_map_keys> \ <second_map_keys>
    std::vector<std::string> get_keys_diff(std::map<std::string, capd::interval>, std::map<std::string, capd::interval>);

    std::vector<std::tuple<int, box>> series_to_boxes(std::map<std::string, std::vector<capd::interval>>);

    // here only one initial mode and one goal mode
    std::string reach_to_smt2(std::vector<pdrh::mode*>, std::vector<box>);
    std::string reach_c_to_smt2(std::vector<pdrh::mode*>, std::vector<box>);

    std::string reach_to_smt2(pdrh::state, pdrh::state, std::vector<pdrh::mode*>, std::vector<box>);
    std::string reach_c_to_smt2(pdrh::state, pdrh::state, std::vector<pdrh::mode*>, std::vector<box>);

    // here only one initial mode and one goal mode
    std::string reach_to_smt2(std::vector<pdrh::mode*>, rv_box*, dd_box*, nd_box*);
    std::string reach_c_to_smt2(std::vector<pdrh::mode*>, rv_box*, dd_box*, nd_box*);

    std::string model_to_string();
    std::string print_jump(pdrh::mode::jump);

    // defined distributions
    namespace distribution
    {
        extern std::map<std::string, std::pair<capd::interval, capd::interval>> uniform;
        extern std::map<std::string, std::pair<capd::interval, capd::interval>> normal;
        extern std::map<std::string, capd::interval> exp;
        extern std::map<std::string, std::pair<capd::interval, capd::interval>> gamma;

        void push_uniform(std::string, capd::interval, capd::interval);
        void push_normal(std::string, capd::interval, capd::interval);
        void push_exp(std::string, capd::interval);
        void push_gamma(std::string, capd::interval, capd::interval);
    }
}


#endif //PROBREACH_MODEL_H
