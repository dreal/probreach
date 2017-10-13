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

using namespace std;

namespace pdrh
{
    // node of the tree of mathematical expression
    struct node
    {
        // either a name of operation or a value of the operand (const or identifier)
        string value;
        // vector is empty if the node is terminal and non-empty if the node is operation node
        vector<node*> operands;

        inline node(const node &rhs)
                : value(rhs.value), operands(rhs.operands)
        {
        }

        inline node(const string value, const vector<node*> operands)
                : value(value), operands(operands)
        {
        }

        inline node(const string value)
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
    node* push_terminal_node(string);
    node* push_operation_node(string, vector<node*>);
    node* copy_node(node*);
    void copy_tree(node*&, node*);

    node* push_terminal_node(double);
    node* push_operation_node(double, vector<node*>);

    string node_to_string_prefix(node*);
    string node_to_string_infix(node*);
    capd::interval node_to_interval(node*);
    capd::interval node_to_interval(node*, box);
    string node_fix_index(node*, int, string);
    bool is_node_empty(node*);

    node* get_first_time_node(node*);
    void get_first_time_node(node*, node*);
    node* get_time_node_neg(node*);

    void push_prob_partition_prec(string, capd::interval);
    void push_nondet_partition_prec(string, capd::interval);

    enum type {HA, PHA, NHA, NPHA, PSY};
    extern type model_type;
    extern pair<node*, node*> time;
    extern map<string, tuple<node*, node*, node*, node*>> rv_map;
    extern map<string, string> rv_type_map;
    extern map<string, map<node*, node*>> dd_map;
    extern map<string, pair<node*, node*>> var_map;
    extern map<string, pair<node*, node*>> par_map;
    extern map<string, node*> syn_map;
    // mode struct
    struct mode
    {
        int id;
        vector<node*> invts;
        // jump struct
        struct jump
        {
            node* guard;
            int next_id;
            map<string, node*> reset;
            map<string, tuple<string, pdrh::node*, pdrh::node*, pdrh::node*, pdrh::node*>> reset_rv;
            map<string, map<node*, node*>> reset_dd;
            map<string, pair<node*, node*>> reset_nondet;
        };
        vector<jump> jumps;
        map<string, pair<node*, node*>> flow_map;
        map<string, node*> odes;
        pair<node*, node*> time;
    };
    extern vector<mode> modes;

    // state struct
    struct state
    {
        int id;
        node* prop;
    };
    extern vector<state> init;
    extern vector<state> goal;
    extern vector<vector<mode*>> paths;
    // methods for updating the model
    void push_var(string, node*, node*);
    void push_dd(string, map<node*, node*>);
    void push_rv(string, node*, node*, node*, node*);
    void push_rv_type(string, string);
    void push_mode(mode);
    void push_invt(mode&, node*);
    // first argument is the address of the mode, second argument is the variable name, third argument is the ode
    void push_ode(mode&, string, node*);
    void push_jump(mode&, mode::jump);
    // first argument is the address of the jump, second argument is the variable name, third argument is the reset expression
    void push_reset(mode&, mode::jump&, string, node*);
    void push_init(vector<state>);
    void push_goal(vector<state>);
    void push_path(vector<mode*>);
    void push_psy_goal(int, box);
    void push_psy_c_goal(int, box);
    void push_syn_pair(string, node*);
    void push_time_bounds(node*, node*);


    void set_model_type();

    box get_nondet_domain();
    box get_psy_domain();
    vector<mode*> get_psy_path(map<string, vector<capd::interval>>);
    vector<mode*> get_psy_path(map<string, vector<pair<pdrh::node*, pdrh::node*>>>);

    vector<tuple<int, box>> series_to_boxes(map<string, vector<capd::interval>>);
    //vector<state> series_to_goals(map<string, vector<pair<pdrh::node*, pdrh::node*>>>);

    bool var_exists(string);
    mode* get_mode(int);

    //void update_resets();

    vector<mode*> get_init_modes();
    vector<mode*> get_goal_modes();
    vector<mode*> get_successors(mode*);
    vector<mode*> get_shortest_path(mode*, mode*);
    vector<vector<mode*>> get_paths(mode*, mode*, int);
    vector<vector<mode*>> get_paths();
    vector<vector<mode*>> get_all_paths(int);
    vector<vector<mode*>> get_all_paths();

    // returns <first_map_keys> \ <second_map_keys>
    vector<string> get_keys_diff(map<string, pair<node*, node*>>, map<string, pair<node*, node*>>);

    // here only one initial mode and one goal mode
    string reach_to_smt2(vector<mode*>, vector<box>);
    string reach_to_smt2(state, state, vector<mode*>, vector<box>);
    string reach_c_to_smt2(vector<mode*>, vector<box>);
    string reach_c_to_smt2(state, state, vector<mode*>, vector<box>);
    string reach_c_to_smt2(int, vector<mode*>, vector<box>);
    string reach_c_to_smt2(state, state, int, vector<mode*>, vector<box>);

    string reach_to_isat(vector<box>);

    string reach_to_smt2_all_paths(vector<box>);
    string reach_c_to_smt2_all_paths();

    string model_to_string();
    string print_jump(mode::jump);

    namespace distribution
    {
        extern map<string, pair<node*, node*>> uniform;
        extern map<string, pair<node*, node*>> normal;
        extern map<string, node*> exp;
        extern map<string, pair<node*, node*>> gamma;

        void push_uniform(string, node*, node*);
        void push_normal(string, node*, node*);
        void push_exp(string, node*);
        void push_gamma(string, node*, node*);

        node* uniform_to_node(node*, node*);
        node* normal_to_node(string, node*, node*);
        node* exp_to_node(string, node*);
        node* gamma_to_node(string, node*, node*);
    }
}

#endif //PROBREACH_MODEL_H
