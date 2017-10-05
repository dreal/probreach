//
// Created by fedor on 22/09/17.
//

#include "ap.h"
#include "pdrh_config.h"
#include "model.h"
#include <capd/capdlib.h>
#include <capd/intervals/lib.h>

pdrh::type ap::model_type;
pair<pdrh::node*, pdrh::node*> ap::time;
map<string, tuple<pdrh::node*, pdrh::node*, pdrh::node*, pdrh::node*>> ap::rv_map;
map<string, string> ap::rv_type_map;
map<string, map<pdrh::node*, pdrh::node*>> ap::dd_map;
map<string, pair<pdrh::node*, pdrh::node*>> ap::var_map;
map<string, pair<pdrh::node*, pdrh::node*>> ap::par_map;
map<string, pdrh::node*> ap::syn_map;
vector<pdrh::mode> ap::modes;
vector<pdrh::state> ap::init;
vector<pdrh::state> ap::goal;
vector<vector<pdrh::mode*>> ap::paths;

map<string, pair<pdrh::node*, pdrh::node*>> ap::distribution::uniform;
map<string, pair<pdrh::node*, pdrh::node*>> ap::distribution::normal;
map<string, pdrh::node*> ap::distribution::exp;
map<string, pair<pdrh::node*, pdrh::node*>> ap::distribution::gamma;

void ap::copy_model()
{
    ap::model_type = pdrh::model_type;
    ap::time = pdrh::time;
    ap::rv_map = pdrh::rv_map;
    ap::rv_type_map = pdrh::rv_type_map;
    ap::dd_map = pdrh::dd_map;
    ap::var_map = pdrh::var_map;
    ap::par_map = pdrh::par_map;
    ap::syn_map = pdrh::syn_map;
    ap::modes = pdrh::modes;
    ap::init = pdrh::init;
    ap::goal = pdrh::goal;
    ap::paths = pdrh::paths;
    ap::distribution::uniform = pdrh::distribution::uniform;
    ap::distribution::normal = pdrh::distribution::normal;
    ap::distribution::exp = pdrh::distribution::exp;
    ap::distribution::gamma = pdrh::distribution::gamma;
}

void ap::modify_model()
{
    // removing all non-time variables
    map<string, pair<pdrh::node*, pdrh::node*>> var_map;
    for(auto it = pdrh::var_map.begin(); it != pdrh::var_map.end(); it++)
    {
        if(std::find(global_config.time_var_name.begin(), global_config.time_var_name.end(), it->first) != global_config.time_var_name.end())
        {
            var_map.insert(make_pair(it->first, it->second));
        }
    }
    pdrh::var_map = var_map;

    // removing all non-time parameters
    map<string, pair<pdrh::node*, pdrh::node*>> par_map;
    for(auto it = pdrh::par_map.begin(); it != pdrh::par_map.end(); it++)
    {
        if(std::find(global_config.time_var_name.begin(), global_config.time_var_name.end(), it->first) != global_config.time_var_name.end())
        {
            par_map.insert(make_pair(it->first, it->second));
        }
    }
    pdrh::par_map = par_map;

    for(int i = 0; i < pdrh::modes.size(); i++)
    {
        // removing non-time variables from the flow map
        map<string, pair<pdrh::node*, pdrh::node*>> flow_map;
        for(auto it = pdrh::modes.at(i).flow_map.begin(); it != pdrh::modes.at(i).flow_map.end(); it++)
        {
            if(std::find(global_config.time_var_name.begin(), global_config.time_var_name.end(), it->first) != global_config.time_var_name.end())
            {
                flow_map.insert(make_pair(it->first, it->second));
            }
        }
        pdrh::modes.at(i).flow_map = flow_map;

        // removing non-time variables from the ode map
        map<string, pdrh::node*> odes;
        for(auto it = pdrh::modes.at(i).odes.begin(); it != pdrh::modes.at(i).odes.end(); it++)
        {
            if(std::find(global_config.time_var_name.begin(), global_config.time_var_name.end(), it->first) != global_config.time_var_name.end())
            {
                odes.insert(make_pair(it->first, it->second));
            }
        }
        pdrh::modes.at(i).odes = odes;

        // removing non-time variables from the resets and the guards
        for(int j = 0; j < pdrh::modes.at(i).jumps.size(); j++)
        {
            // removing non-time variables from the resets
            map<string, pdrh::node*> reset;
            for(auto it = pdrh::modes.at(i).jumps.at(j).reset.begin(); it != pdrh::modes.at(i).jumps.at(j).reset.end(); it++)
            {
                if(std::find(global_config.time_var_name.begin(), global_config.time_var_name.end(), it->first) != global_config.time_var_name.end())
                {
                    reset.insert(make_pair(it->first, it->second));
                }
            }
            pdrh::modes.at(i).jumps.at(j).reset = reset;

            // removing non-time variables from the dd map
            map<string, map<pdrh::node*, pdrh::node*>> reset_dd;
            for(auto it = pdrh::modes.at(i).jumps.at(j).reset_dd.begin(); it != pdrh::modes.at(i).jumps.at(j).reset_dd.end(); it++)
            {
                if(std::find(global_config.time_var_name.begin(), global_config.time_var_name.end(), it->first) != global_config.time_var_name.end())
                {
                    reset_dd.insert(make_pair(it->first, it->second));
                }
            }
            pdrh::modes.at(i).jumps.at(j).reset_dd = reset_dd;

            // removing non-time variables from the rv map
            map<string, tuple<string, pdrh::node*, pdrh::node*, pdrh::node*, pdrh::node*>> reset_rv;
            for(auto it = pdrh::modes.at(i).jumps.at(j).reset_rv.begin(); it != pdrh::modes.at(i).jumps.at(j).reset_rv.end(); it++)
            {
                cout << it->first << endl;
                if(std::find(global_config.time_var_name.begin(), global_config.time_var_name.end(), it->first) != global_config.time_var_name.end())
                {
                    reset_rv.insert(make_pair(it->first, it->second));
                }
            }
            pdrh::modes.at(i).jumps.at(j).reset_rv = reset_rv;

            // removing non-time variables from the nondet map
            map<string, pair<pdrh::node*, pdrh::node*>> reset_nondet;
            for(auto it = pdrh::modes.at(i).jumps.at(j).reset_nondet.begin(); it != pdrh::modes.at(i).jumps.at(j).reset_nondet.end(); it++)
            {
                if(std::find(global_config.time_var_name.begin(), global_config.time_var_name.end(), it->first) != global_config.time_var_name.end())
                {
                    reset_nondet.insert(make_pair(it->first, it->second));
                }
            }
            pdrh::modes.at(i).jumps.at(j).reset_nondet = reset_nondet;
        }

    }

    // pdrh::modes.clear();
    // pdrh::init.clear();
    // pdrh::goal.clear();
    // pdrh::paths.clear();
}

void ap::nullify_odes()
{
    for(int i = 0; i < pdrh::modes.size(); i++)
    {
        // removing non-time variables from the ode map
        for(auto it = pdrh::modes.at(i).odes.begin(); it != pdrh::modes.at(i).odes.end(); it++)
        {
            if(std::find(global_config.time_var_name.begin(), global_config.time_var_name.end(), it->first) == global_config.time_var_name.end())
            {
                it->second = new pdrh::node("0");
            }
        }
    }
}

void ap::revert_model()
{
    pdrh::model_type = ap::model_type;
    pdrh::time = ap::time;
    pdrh::rv_map = ap::rv_map;
    pdrh::rv_type_map = ap::rv_type_map;
    pdrh::dd_map = ap::dd_map;
    pdrh::var_map = ap::var_map;
    pdrh::par_map = ap::par_map;
    pdrh::syn_map = ap::syn_map;
    pdrh::modes = ap::modes;
    pdrh::init = ap::init;
    pdrh::goal = ap::goal;
    pdrh::paths = ap::paths;
    pdrh::distribution::uniform = ap::distribution::uniform;
    pdrh::distribution::normal = ap::distribution::normal;
    pdrh::distribution::exp = ap::distribution::exp;
    pdrh::distribution::gamma = ap::distribution::gamma;
}

capd::interval ap::get_sample_rate(pdrh::node* n)
{
    pdrh::node *node_copy = new pdrh::node;
    pdrh::copy_tree(node_copy, n);
    pdrh::node* time_node = new pdrh::node;
    pdrh::get_first_time_node(node_copy, time_node);
    // checking if the time node is not empty
    if(!pdrh::is_node_empty(time_node))
    {
        // checking if the time node signature is <var>=<value>
        if(time_node->value == "=")
        {
            if(time_node->operands.front()->value == "counter")
            {
                return pdrh::node_to_interval(time_node->operands.back());
            }
            if(time_node->operands.back()->value == "counter")
            {
                return pdrh::node_to_interval(time_node->operands.front());
            }
        }
    }
    return capd::interval(0.0);
}


capd::interval ap::get_sample_rate(pdrh::mode* m)
{
    for(pdrh::mode::jump j : m->jumps)
    {
        capd::interval sample_rate = ap::get_sample_rate(j.guard);
        if(sample_rate != capd::interval(0.0))
        {
            return sample_rate;
        }
    }
    return capd::interval(0.0);
}


capd::interval ap::get_meal_time(pdrh::node *n, vector<box> boxes)
{
    pdrh::node *node_copy = new pdrh::node();
    pdrh::copy_tree(node_copy, n);
    pdrh::node* time_node = new pdrh::node;
    pdrh::get_first_time_node(node_copy, time_node);
    // checking if the time node is not empty
    if(!pdrh::is_node_empty(time_node))
    {
        // checking if the time node signature is <var>=<value>
        if(time_node->value == "=")
        {
            if(time_node->operands.front()->value == "tau")
            {
                for(box b : boxes)
                {
                    for(auto it = b.get_map().begin(); it != b.get_map().end(); it++)
                    {
                        if(it->first == time_node->operands.back()->value)
                        {
                            return it->second;
                        }
                    }
                }
                return pdrh::node_to_interval(time_node->operands.back());
            }
            if(time_node->operands.back()->value == "tau")
            {
                for(box b : boxes)
                {
                    for(auto it = b.get_map().begin(); it != b.get_map().end(); it++)
                    {
                        if(it->first == time_node->operands.front()->value)
                        {
                            return it->second;
                        }
                    }
                }
                return pdrh::node_to_interval(time_node->operands.front());
            }
        }
    }
    return capd::interval(0.0);
}


capd::interval ap::get_meal_time(pdrh::mode *m, vector<box> boxes)
{
    for(pdrh::mode::jump j : m->jumps)
    {
        capd::interval meal_time = ap::get_meal_time(j.guard, boxes);
        if(meal_time != capd::interval(0.0))
        {
            return meal_time;
        }
    }
    return capd::interval(0.0);
}


int ap::jumps_per_mode(pdrh::mode *m)
{
    capd::interval sample_rate = ap::get_sample_rate(m);
    for(pdrh::state st : pdrh::goal)
    {
        if(m->id == st.id)
        {
            cout << fmod(ap::get_meal_time(st.prop, {}).rightBound(), sample_rate.rightBound()) << endl;
            return ceil((ap::get_meal_time(st.prop, {}) / sample_rate).rightBound());
        }
    }
    return ceil((ap::get_meal_time(m, {}) / sample_rate).rightBound());
}



