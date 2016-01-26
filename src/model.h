//
// Created by fedor on 24/01/16.
//

#ifndef PROBREACH_MODEL_H
#define PROBREACH_MODEL_H

#include <iostream>
#include <vector>
#include <map>
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>

namespace pdrh
{
    extern int type;
    extern capd::interval time;
    extern std::map<std::string, std::string> rv_map;
    extern std::map<std::string, std::map<capd::interval, capd::interval>> dd_map;
    extern std::map<std::string, capd::interval> var_map;
    extern std::map<std::string, double> syn_map;
    // mode struct
    struct mode
    {
        int id;
        std::vector<std::string> invts;
        // jump struct
        struct jump
        {
            std::string guard;
            int next_id;
            std::map<std::string, std::string> reset;
        };
        std::vector<jump> jumps;
        std::map<std::string, capd::interval> flow_map;
        std::map<std::string, std::string> odes;
    };
    extern std::vector<mode> modes;
    // state struct
    struct state
    {
        int id;
        std::string prop;
    };
    extern std::vector<state> init;
    extern std::vector<state> goal;

    void push_var(std::string, capd::interval);
    void push_rv(std::string, std::string);
    void push_dd(std::string, std::map<capd::interval, capd::interval>);
    void push_mode(pdrh::mode);
    void push_invt(pdrh::mode&, std::string);
    // first argument is the address of the mode, second argument is the variable name, third argument is the ode
    void push_ode(pdrh::mode&, std::string, std::string);
    void push_jump(pdrh::mode&, pdrh::mode::jump);
    // first argument is the address of the jump, second argument is the variable name, third argument is the reset expression
    void push_reset(pdrh::mode&, pdrh::mode::jump&, std::string, std::string);
    void push_init(std::vector<pdrh::state>);
    void push_goal(std::vector<pdrh::state>);
    void push_syn_pair(std::string, double);
    void push_time_bounds(capd::interval);

    bool check_var(std::string);

    std::string print_model();

}


#endif //PROBREACH_MODEL_H
