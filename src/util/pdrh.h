//
// Created by fedor on 24/01/16.
//

#ifndef PROBREACH_MODEL_H
#define PROBREACH_MODEL_H

#include <iostream>
#include <vector>
#include <map>
#include <tuple>
#include "node.h"

namespace pdrh
{
    node* get_first_time_node(node*);
    void get_first_time_node(node*, node*);
    node* get_time_node_neg(node*);

    enum type {HA, PHA, NHA, NPHA, PSY};
    extern type model_type;
    extern std::pair<node*, node*> time;
    extern std::map<std::string, std::tuple<node*, node*, node*, node*>> rv_map;
    extern std::map<std::string, std::string> rv_type_map;
    extern std::map<std::string, std::map<node*, node*>> dd_map;
    extern std::map<std::string, std::pair<node*, node*>> var_map;
    extern std::map<std::string, std::pair<node*, node*>> par_map;
    extern std::map<std::string, std::string> const_map;
    extern std::map<std::string, node*> syn_map;
    // mode struct
    struct mode
    {
        int id;
        std::vector<node*> invts;
        // jump struct
        struct jump
        {
            node* guard;
            int next_id;
            std::map<std::string, node*> reset;
            std::map<std::string, std::tuple<std::string, pdrh::node*, pdrh::node*, pdrh::node*, pdrh::node*>> reset_rv;
            std::map<std::string, std::map<node*, node*>> reset_dd;
            std::map<std::string, std::pair<node*, node*>> reset_nondet;
        };
        std::vector<jump> jumps;
        std::map<std::string, std::pair<node*, node*>> flow_map;
        std::map<std::string, node*> odes;
        std::pair<node*, node*> time;

        pdrh::mode::jump get_jump(int);
    };
    extern std::vector<mode> modes;

    // state struct
    struct state
    {
        int id;
        node* prop;

        inline state(const int id, node* prop)
                : id(id), prop(prop)
        {
        }

        inline state()
        {
        }

        friend std::ostream& operator<<(std::ostream &os, const pdrh::state &st)
        {
            os << st.id << ":" << pdrh::node_to_string_prefix(st.prop) << ";";
            return os;
        }
    };
    extern std::vector<state> init;
    extern std::vector<state> goal;
    extern std::vector<std::vector<mode*>> paths;
    // methods for updating the model
    void push_var(std::string, node*, node*);
    void push_dd(std::string, std::map<node*, node*>);
    void push_rv(std::string, node*, node*, node*, node*);
    void push_rv_type(std::string, std::string);
    void push_mode(mode);
    void push_invt(mode&, node*);
    // first argument is the address of the mode, second argument is the variable name, third argument is the ode
    void push_ode(mode&, std::string, node*);
    void push_jump(mode&, mode::jump);
    // first argument is the address of the jump, second argument is the variable name, third argument is the reset expression
    void push_reset(mode&, mode::jump&, std::string, node*);
    void push_init(std::vector<state>);
    void push_goal(std::vector<state>);
    void push_path(std::vector<mode*>);
//    void push_psy_goal(int, box);
//    void push_psy_c_goal(int, box);
    void push_syn_pair(std::string, node*);
    void push_time_bounds(node*, node*);

    void set_model_type();

//    std::vector<mode*> get_psy_path(std::map<std::string, std::vector<capd::interval>>);
    std::vector<mode*> get_psy_path(std::map<std::string, std::vector<std::pair<pdrh::node*, pdrh::node*>>>);

//    vector<tuple<int, box>> series_to_boxes(std::map<std::string, std::vector<capd::interval>>);
    //vector<state> series_to_goals(map<string, vector<pair<pdrh::node*, pdrh::node*>>>);

    bool var_exists(std::string);
    mode* get_mode(int);


    //void update_resets();

    std::vector<mode*> get_init_modes();
    std::vector<mode*> get_goal_modes();
    std::vector<mode*> get_successors(mode*);
    std::vector<mode*> get_shortest_path(mode*, mode*);
    std::vector<std::vector<mode*>> get_paths(mode*, mode*, int);
    std::vector<std::vector<mode*>> get_paths();
    std::vector<std::vector<mode*>> get_all_paths(int);
    std::vector<std::vector<mode*>> get_all_paths();

    // returns <first_map_keys> \ <second_map_keys>
    std::vector<std::string> get_keys_diff(std::map<std::string, std::pair<node*, node*>>, std::map<std::string, std::pair<node*, node*>>);

    std::string model_to_string();
    std::string print_jump(mode::jump);

    namespace distribution
    {
        extern std::map<std::string, std::pair<node*, node*>> uniform;
        extern std::map<std::string, std::pair<node*, node*>> normal;
        extern std::map<std::string, node*> exp;
        extern std::map<std::string, std::pair<node*, node*>> gamma;

        void push_uniform(std::string, node*, node*);
        void push_normal(std::string, node*, node*);
        void push_exp(std::string, node*);
        void push_gamma(std::string, node*, node*);

        node* uniform_to_node(node*, node*);
        node* normal_to_node(std::string, node*, node*);
        node* exp_to_node(std::string, node*);
        node* gamma_to_node(std::string, node*, node*);
    }
}


#endif //PROBREACH_MODEL_H
