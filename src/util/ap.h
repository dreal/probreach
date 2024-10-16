//
// Created by fedor on 22/09/17.
//

#ifndef PROBREACH_AP_H
#define PROBREACH_AP_H

#include <iostream>
#include <vector>
#include <map>
#include <capd/capdlib.h>
#include <capd/intervals/lib.h>
#include <tuple>
#include "box.h"
#include "model.h"

namespace ap
{
extern std::vector<box> unsat_samples;

//    void get_first_time_node(pdrh::node*, pdrh::node*);
//    pdrh::node* get_time_node_neg(pdrh::node*);

capd::interval get_sample_rate(pdrh::node *);
capd::interval get_sample_rate(pdrh::mode *);

capd::interval get_meal_time(pdrh::node *, std::vector<box>);
capd::interval get_meal_time(pdrh::mode *, std::vector<box>);

int jumps_per_mode(pdrh::mode *, std::vector<box>);

// current and previous mode
int jumps_per_mode(pdrh::mode *, pdrh::mode *, std::vector<box>);

bool accept_path(std::vector<pdrh::mode *>, std::vector<box>);
std::vector<std::vector<pdrh::mode *>> get_all_paths(std::vector<box>);

//    box init_to_box(vector<box>);

box solve_odes(
  std::map<std::string, pdrh::node *>,
  box,
  capd::interval,
  std::vector<box>);
box solve_odes_nonrig(
  std::map<std::string, pdrh::node *>,
  box,
  capd::interval,
  std::vector<box>);
box solve_odes_discrete(
  std::map<std::string, pdrh::node *>,
  box,
  capd::interval,
  size_t,
  std::vector<box>);

int simulate_path(std::vector<pdrh::mode *>, box, std::vector<box>);

// The last argument is the list of variables defining the objective function
box compute_objective(
  std::vector<pdrh::mode *>,
  box,
  std::vector<box>,
  std::vector<std::string>);
capd::interval
  compute_robustness(std::vector<pdrh::mode *>, box, std::vector<box>);
capd::interval compute_max_robustness(
  std::vector<std::vector<pdrh::mode *>>,
  box,
  std::vector<box>);
capd::interval compute_min_robustness(
  std::vector<std::vector<pdrh::mode *>>,
  box,
  std::vector<box>);

bool check_invariants(pdrh::mode *, box, std::vector<box>);

int verify(size_t, size_t, std::vector<box>);
int simulate(size_t, size_t, std::vector<box>);

bool is_sample_jump(pdrh::mode::jump);
box apply_reset(std::map<std::string, pdrh::node *>, box, std::vector<box>);
} // namespace ap

#endif //PROBREACH_AP_H
