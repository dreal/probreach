//
// Created by fedor on 06/11/17.
//

#include "smt2_generator.h"

#include "pdrh_config.h"

using namespace std;
using namespace capd;
using namespace pdrh;

string smt2_generator::generate_flow_invt_check(mode* m, interval time,
                                                box init, vector<box> boxes) {
  stringstream s;
  s.precision(16);

  // declaring the logic type
  s << "(set-logic QF_NRA_ODE)" << endl;

  // declaring functions and their bounds
  s << "; declaring functions and their bounds" << endl;
  for (auto it = m->flow_map.begin(); it != m->flow_map.end(); it++) {
    s << "(declare-fun " << it->first << " () Real)" << endl;
    s << "(declare-fun " << it->first << "_0_0 () Real)" << endl;
    s << "(declare-fun " << it->first << "_0_t () Real)" << endl;
    if (it->second.first->value != "-infty") {
      s << "(assert (>= " << it->first << "_0_0 "
        << node_to_string_prefix(it->second.first) << "))" << endl;
      s << "(assert (>= " << it->first << "_0_t "
        << node_to_string_prefix(it->second.first) << "))" << endl;
    }
    if (it->second.second->value != "infty") {
      s << "(assert (<= " << it->first << "_0_0 "
        << node_to_string_prefix(it->second.second) << "))" << endl;
      s << "(assert (<= " << it->first << "_0_t "
        << node_to_string_prefix(it->second.second) << "))" << endl;
    }
  }

  // assigning the values for the provided samples
  s << "; assigning the values of the sample" << endl;
  for (box b : boxes) {
    std::map<string, interval> b_map = b.get_map();
    for (auto it = b_map.begin(); it != b_map.end(); it++) {
      s << "(assert (>= " << it->first << "_0_0 " << it->second.leftBound()
        << "))" << endl;
      s << "(assert (>= " << it->first << "_0_t " << it->second.leftBound()
        << "))" << endl;
      s << "(assert (<= " << it->first << "_0_0 " << it->second.rightBound()
        << "))" << endl;
      s << "(assert (<= " << it->first << "_0_t " << it->second.rightBound()
        << "))" << endl;
    }
  }

  // declaring time
  s << "; declaring time variable and integration bounds" << endl;
  s << "(declare-fun time () Real)" << endl;
  s << "(assert (>= time 0.0))" << endl;
  s << "(assert (<= time " << time.rightBound() << "))" << endl;

  // declaring a variable mocking the time variable
  // not needed for the complement formula
  s << "; declaring a variable mocking the time variable" << endl;
  s << "(declare-fun time_mock () Real)" << endl;
  s << "(declare-fun time_mock_0_0 () Real)" << endl;
  s << "(declare-fun time_mock_0_t () Real)" << endl;

  // defining odes
  s << "; defining odes" << endl;
  s << "(define-ode flow_" << m->id << " (";
  for (auto it = m->odes.begin(); it != m->odes.end(); it++) {
    s << "(= d/dt[" << it->first << "] " << node_to_string_prefix(it->second)
      << ")" << endl;
  }

  // declaring an ode for time_mock variable
  // not needed for the complement formula
  s << "(= d/dt[time_mock] 1.0)" << endl;
  s << "))" << endl;

  // defining initial condition
  s << "; defining initial condition" << endl;
  std::map<string, interval> b_map = init.get_map();
  for (auto it = b_map.begin(); it != b_map.end(); it++) {
    s << "(assert (and (>= " << it->first << "_0_0 " << it->second.leftBound()
      << ") "
      << "(<= " << it->first << "_0_0 " << it->second.rightBound() << ")))"
      << endl;
  }

  // defining the integral
  s << "; defining the integral" << endl;
  s << "(assert (= [";
  for (auto it = m->odes.cbegin(); it != m->odes.cend(); it++) {
    s << it->first << "_0_t ";
  }
  s << "time_mock_0_t] (integral 0.0 time [";
  for (auto it = m->odes.cbegin(); it != m->odes.cend(); it++) {
    s << it->first << "_0_0 ";
  }
  s << "time_mock_0_0] flow_" << m->id << ")))" << endl;

  // defining invariants
  s << "; defining invariants" << endl;
  for (node* invt : m->invts) {
    s << "(assert (forall_t " << m->id << " [0.0 time] "
      << pdrh::node_fix_index(invt, 0, "t") << "))" << endl;
  }

  // defining the goal for the time mock variable
  s << "; defining goal for the time mock variable" << endl;
  s << "(assert (= time_mock_0_0 0.0))" << endl;
  s << "(assert (= time_mock_0_t " << time.rightBound() << "))" << endl;

  s << "(check-sat)" << endl;
  s << "(exit)" << endl;

  return s.str();
}

string smt2_generator::generate_flow_invt_check_c(mode* m, interval time,
                                                  box init, vector<box> boxes) {
  stringstream s;
  s.precision(16);

  // declaring the logic type
  s << "(set-logic QF_NRA_ODE)" << endl;

  // declaring functions and their bounds
  s << "; declaring functions and their bounds" << endl;
  for (auto it = m->flow_map.begin(); it != m->flow_map.end(); it++) {
    s << "(declare-fun " << it->first << " () Real)" << endl;
    s << "(declare-fun " << it->first << "_0_0 () Real)" << endl;
    s << "(declare-fun " << it->first << "_0_t () Real)" << endl;
    if (it->second.first->value != "-infty") {
      s << "(assert (>= " << it->first << "_0_0 "
        << node_to_string_prefix(it->second.first) << "))" << endl;
      s << "(assert (>= " << it->first << "_0_t "
        << node_to_string_prefix(it->second.first) << "))" << endl;
    }
    if (it->second.second->value != "infty") {
      s << "(assert (<= " << it->first << "_0_0 "
        << node_to_string_prefix(it->second.second) << "))" << endl;
      s << "(assert (<= " << it->first << "_0_t "
        << node_to_string_prefix(it->second.second) << "))" << endl;
    }
  }

  // assigning the values for the provided samples
  s << "; assigning the values of the sample" << endl;
  for (box b : boxes) {
    std::map<string, interval> b_map = b.get_map();
    for (auto it = b_map.begin(); it != b_map.end(); it++) {
      s << "(assert (>= " << it->first << "_0_0 " << it->second.leftBound()
        << "))" << endl;
      s << "(assert (>= " << it->first << "_0_t " << it->second.leftBound()
        << "))" << endl;
      s << "(assert (<= " << it->first << "_0_0 " << it->second.rightBound()
        << "))" << endl;
      s << "(assert (<= " << it->first << "_0_t " << it->second.rightBound()
        << "))" << endl;
    }
  }

  // declaring time
  s << "; declaring time variable and integration bounds" << endl;
  s << "(declare-fun time () Real)" << endl;
  s << "(assert (>= time 0.0))" << endl;
  s << "(assert (<= time " << time.rightBound() << "))" << endl;

  // defining odes
  s << "; defining odes" << endl;
  s << "(define-ode flow_" << m->id << " (";
  for (auto it = m->odes.begin(); it != m->odes.end(); it++) {
    s << "(= d/dt[" << it->first << "] " << node_to_string_prefix(it->second)
      << ")" << endl;
  }
  s << "))" << endl;

  // defining initial condition
  s << "; defining initial condition" << endl;
  std::map<string, interval> b_map = init.get_map();
  for (auto it = b_map.begin(); it != b_map.end(); it++) {
    s << "(assert (and (>= " << it->first << "_0_0 " << it->second.leftBound()
      << ") "
      << "(<= " << it->first << "_0_0 " << it->second.rightBound() << ")))"
      << endl;
  }

  // defining the integral
  s << "; defining the integral" << endl;
  s << "(assert (= [";
  for (auto it = m->odes.cbegin(); it != m->odes.cend(); it++) {
    s << it->first << "_0_t ";
  }
  s << "] (integral 0.0 time [";
  for (auto it = m->odes.cbegin(); it != m->odes.cend(); it++) {
    s << it->first << "_0_0 ";
  }
  s << "] flow_" << m->id << ")))" << endl;

  // defining invariants negations
  s << "; defining invariants negations" << endl;
  s << "(assert (or" << endl;
  for (node* invt : m->invts) {
    s << "(not " << pdrh::node_fix_index(invt, 0, "t") << ")" << endl;
  }
  s << "))" << endl;

  s << "(check-sat)" << endl;
  s << "(exit)" << endl;

  return s.str();
}

string smt2_generator::generate_jump_check(mode* m, vector<mode::jump> jumps,
                                           box init, vector<box> boxes) {
  stringstream s;
  s.precision(16);

  // declaring the logic type
  s << "(set-logic QF_NRA_ODE)" << endl;

  // declaring functions and their bounds
  s << "; declaring functions and their bounds" << endl;
  for (auto it = m->flow_map.begin(); it != m->flow_map.end(); it++) {
    s << "(declare-fun " << it->first << " () Real)" << endl;
    s << "(declare-fun " << it->first << "_0_0 () Real)" << endl;
    s << "(declare-fun " << it->first << "_0_t () Real)" << endl;
    if (it->second.first->value != "-infty") {
      s << "(assert (>= " << it->first << "_0_0 "
        << node_to_string_prefix(it->second.first) << "))" << endl;
      s << "(assert (>= " << it->first << "_0_t "
        << node_to_string_prefix(it->second.first) << "))" << endl;
    }
    if (it->second.second->value != "infty") {
      s << "(assert (<= " << it->first << "_0_0 "
        << node_to_string_prefix(it->second.second) << "))" << endl;
      s << "(assert (<= " << it->first << "_0_t "
        << node_to_string_prefix(it->second.second) << "))" << endl;
    }
  }

  // assigning the values for the provided samples
  s << "; assigning the values of the sample" << endl;
  for (box b : boxes) {
    std::map<string, interval> b_map = b.get_map();
    for (auto it = b_map.begin(); it != b_map.end(); it++) {
      s << "(assert (>= " << it->first << "_0_0 " << it->second.leftBound()
        << "))" << endl;
      s << "(assert (>= " << it->first << "_0_t " << it->second.leftBound()
        << "))" << endl;
      s << "(assert (<= " << it->first << "_0_0 " << it->second.rightBound()
        << "))" << endl;
      s << "(assert (<= " << it->first << "_0_t " << it->second.rightBound()
        << "))" << endl;
    }
  }

  // declaring time
  s << "; declaring time variable and integration bounds" << endl;
  s << "(declare-fun time () Real)" << endl;
  s << "(assert (>= time " << pdrh::node_to_string_prefix(m->time.first) << "))"
    << endl;
  s << "(assert (<= time " << pdrh::node_to_string_prefix(m->time.second)
    << "))" << endl;

  // declaring a variable mocking the time variable
  // not needed for the complement formula
  s << "; declaring a variable mocking the time variable" << endl;
  s << "(declare-fun time_mock () Real)" << endl;
  s << "(declare-fun time_mock_0_0 () Real)" << endl;
  s << "(declare-fun time_mock_0_t () Real)" << endl;

  // defining odes
  s << "; defining odes" << endl;
  s << "(define-ode flow_" << m->id << " (";
  for (auto it = m->odes.begin(); it != m->odes.end(); it++) {
    s << "(= d/dt[" << it->first << "] " << node_to_string_prefix(it->second)
      << ")" << endl;
  }

  // declaring an ode for time_mock variable
  // not needed for the complement formula
  s << "(= d/dt[time_mock] 1.0)" << endl;
  s << "))" << endl;

  // defining initial condition
  s << "; defining initial condition" << endl;
  std::map<string, interval> b_map = init.get_map();
  for (auto it = b_map.begin(); it != b_map.end(); it++) {
    s << "(assert (and (>= " << it->first << "_0_0 " << it->second.leftBound()
      << ") "
      << "(<= " << it->first << "_0_0 " << it->second.rightBound() << ")))"
      << endl;
  }

  // defining the integral
  s << "; defining the integral" << endl;
  s << "(assert (= [";
  for (auto it = m->odes.cbegin(); it != m->odes.cend(); it++) {
    s << it->first << "_0_t ";
  }
  s << "time_mock_0_t] (integral 0.0 time [";
  for (auto it = m->odes.cbegin(); it != m->odes.cend(); it++) {
    s << it->first << "_0_0 ";
  }
  s << "time_mock_0_0] flow_" << m->id << ")))" << endl;

  // defining jumps
  s << "; defining jumps" << endl;
  s << "(assert (or " << endl;
  for (mode::jump jump : jumps) {
    //        if(jump.guard->operands.front()->value != "counter" &&
    //        jump.guard->operands.back()->value != "counter")
    //        {
    s << pdrh::node_fix_index(jump.guard, 0, "t") << endl;
    //        }
  }
  s << "))" << endl;

  // defining the goal for the time mock variable
  // mock time variable is not used in the check
  s << "; defining goal for the time mock variable" << endl;
  s << "(assert (= time_mock_0_0 0.0))" << endl;
  s << "(assert (>= time_mock_0_t 0.0))" << endl;

  s << "(check-sat)" << endl;
  s << "(exit)" << endl;

  return s.str();
}

// getting a string representation of reachability formula in smt2 format for
// all combinations of initial and goal modes
string smt2_generator::reach_to_smt2(vector<pdrh::mode*> path,
                                     vector<box> boxes) {
  stringstream s;
  s.precision(16);
  // setting logic
  s << "(set-logic QF_NRA_ODE)" << endl;
  // declaring variables and defining bounds (for both variables:
  // at the beginning and at the end of the mode)
  for (auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++) {
    s << "(declare-fun " << it->first << " () Real)" << endl;
    for (int i = 0; i < path.size(); i++) {
      s << "(declare-fun " << it->first << "_" << i << "_0 () Real)" << endl;
      s << "(declare-fun " << it->first << "_" << i << "_t () Real)" << endl;
      if (it->second.first->value != "-infty") {
        s << "(assert (>= " << it->first << "_" << i << "_0 "
          << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
        s << "(assert (>= " << it->first << "_" << i << "_t "
          << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
      }
      if (it->second.second->value != "infty") {
        s << "(assert (<= " << it->first << "_" << i << "_0 "
          << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
        s << "(assert (<= " << it->first << "_" << i << "_t "
          << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
      }
    }
  }
  // declaring time
  for (int i = 0; i < path.size(); i++) {
    s << "(declare-fun time_" << i << " () Real)" << endl;
    s << "(assert (>= time_" << i << " "
      << pdrh::node_fix_index(path.at(i)->time.first, i, "0") << "))" << endl;
    s << "(assert (<= time_" << i << " "
      << pdrh::node_fix_index(path.at(i)->time.second, i, "0") << "))" << endl;
  }
  // defining odes
  for (auto path_it = path.cbegin(); path_it != path.cend(); path_it++) {
    if (find(path.cbegin(), path_it, *path_it) == path_it) {
      s << "(define-ode flow_" << (*path_it)->id << " (";
      for (auto ode_it = (*path_it)->odes.cbegin();
           ode_it != (*path_it)->odes.cend(); ode_it++) {
        s << "(= d/dt[" << ode_it->first << "] "
          << pdrh::node_to_string_prefix(ode_it->second) << ")";
      }
      s << "))" << endl;
    }
  }
  // defining the reachability formula
  s << "(assert (and " << endl;
  // defining initial states
  s << "(or ";
  // putting all initial states into a disjunction
  for (pdrh::state st : pdrh::init) {
    if (st.id == path.front()->id) {
      s << "(" << pdrh::node_fix_index(st.prop, 0, "0") << ")" << endl;
    }
  }
  s << ")" << endl;
  // defining bounds for the parameter boxes
  for (box b : boxes) {
    std::map<string, capd::interval> m = b.get_map();
    for (int i = 0; i < path.size(); i++) {
      for (auto it = m.cbegin(); it != m.cend(); it++) {
        s << "(>= " << it->first << "_" << i << "_0 " << it->second.leftBound()
          << ")" << endl;
        s << "(<= " << it->first << "_" << i << "_0 " << it->second.rightBound()
          << ")" << endl;
        s << "(>= " << it->first << "_" << i << "_t " << it->second.leftBound()
          << ")" << endl;
        s << "(<= " << it->first << "_" << i << "_t " << it->second.rightBound()
          << ")" << endl;
      }
    }
  }
  // defining trajectory
  int step = 0;
  for (pdrh::mode* m : path) {
    // defining integrals
    s << "(= [";
    for (auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++) {
      s << ode_it->first << "_" << step << "_t ";
    }
    s << "] (integral 0.0 time_" << step << " [";
    for (auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++) {
      s << ode_it->first << "_" << step << "_0 ";
    }
    s << "] flow_" << m->id << "))" << endl;
    // defining invariants
    for (pdrh::node* invt : m->invts) {
      s << "(forall_t " << m->id << " [0.0 time_" << step << "] "
        << pdrh::node_fix_index(invt, step, "t") << ")" << endl;
    }
    // checking the current depth
    if (step < path.size() - 1) {
      // defining jumps
      for (pdrh::mode::jump j : m->jumps) {
        // only the jumps to the next mode in the path
        if (j.next_id == path.at(step + 1)->id) {
          s << pdrh::node_fix_index(j.guard, step, "t") << endl;
          for (auto reset_it = j.reset.cbegin(); reset_it != j.reset.cend();
               reset_it++) {
            s << "(= " << reset_it->first << "_" << step + 1 << "_0 "
              << pdrh::node_fix_index(reset_it->second, step, "t") << ")";
          }
        }
      }
    }
    step++;
  }
  // defining goal
  s << "(or ";
  for (pdrh::state st : pdrh::goal) {
    if (st.id == path.back()->id) {
      s << "(" << pdrh::node_fix_index(st.prop, path.size() - 1, "t") << ")";
    }
  }
  s << ")))" << endl;
  // final statements
  s << "(check-sat)" << endl;
  s << "(exit)" << endl;
  return s.str();
}

string smt2_generator::reach_c_to_smt2(vector<pdrh::mode*> path,
                                       vector<box> boxes) {
  stringstream s;
  s.precision(16);
  // setting logic
  s << "(set-logic QF_NRA_ODE)" << endl;
  // checking whether either of last jumps have a time node
  //    pdrh::node* timed_node_neg;
  //    for(pdrh::state st : pdrh::goal)
  //    {
  //        timed_node_neg = pdrh::get_time_node_neg(st.prop);
  //        if(timed_node_neg)
  //        {
  //            break;
  //        }
  //    }
  // declaring variables and defining bounds (at the beginning and
  // at the end of the mode)
  for (auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++) {
    s << "(declare-fun " << it->first << " () Real)" << endl;
    for (int i = 0; i < path.size(); i++) {
      s << "(declare-fun " << it->first << "_" << i << "_0 () Real)" << endl;
      s << "(declare-fun " << it->first << "_" << i << "_t () Real)" << endl;
      if (it->second.first->value != "-infty") {
        s << "(assert (>= " << it->first << "_" << i << "_0 "
          << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
        s << "(assert (>= " << it->first << "_" << i << "_t "
          << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
      }
      if (it->second.second->value != "infty") {
        s << "(assert (<= " << it->first << "_" << i << "_0 "
          << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
        s << "(assert (<= " << it->first << "_" << i << "_t "
          << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
      }
    }
  }
  // declaring time
  for (int i = 0; i < path.size(); i++) {
    s << "(declare-fun time_" << i << " () Real)" << endl;
    s << "(assert (>= time_" << i << " "
      << pdrh::node_fix_index(path.at(i)->time.first, i, "0") << "))" << endl;
    s << "(assert (<= time_" << i << " "
      << pdrh::node_fix_index(path.at(i)->time.second, i, "0") << "))" << endl;
  }
  // declaring local times and its bounds
  // if (!timed_node_neg)
  //{
  s << "(declare-fun local_time () Real)" << endl;
  for (unsigned long i = 0; i < path.size() - 1; i++) {
    s << "(declare-fun local_time_" << i << "_0 () Real)" << endl;
    s << "(declare-fun local_time_" << i << "_t () Real)" << endl;
    s << "(assert (= local_time_" << i << "_0 "
      << pdrh::node_fix_index(path.at(i)->time.first, i, "0") << "))" << endl;
    s << "(assert (>= local_time_" << i << "_t "
      << pdrh::node_fix_index(path.at(i)->time.first, i, "0") << "))" << endl;
    s << "(assert (<= local_time_" << i << "_t "
      << pdrh::node_fix_index(path.at(i)->time.second, i, "0") << "))" << endl;
  }
  // last mode
  // s << "(declare-fun local_time () Real)" << endl;
  s << "(declare-fun local_time_" << path.size() - 1 << "_0 () Real)" << endl;
  s << "(declare-fun local_time_" << path.size() - 1 << "_t () Real)" << endl;
  s << "(assert (= local_time_" << path.size() - 1 << "_0 "
    << pdrh::node_fix_index(path.back()->time.first, path.size() - 1, "0")
    << "))" << endl;
  s << "(assert (>= local_time_" << path.size() - 1 << "_t "
    << pdrh::node_fix_index(path.back()->time.first, path.size() - 1, "0")
    << "))" << endl;
  s << "(assert (<= local_time_" << path.size() - 1 << "_t "
    << pdrh::node_fix_index(path.back()->time.second, path.size() - 1, "0")
    << "))" << endl;
  //}
  // defining odes
  for (auto path_it = path.cbegin(); path_it != path.cend(); path_it++) {
    if (std::find(path.cbegin(), path_it, *path_it) == path_it) {
      s << "(define-ode flow_" << (*path_it)->id << " (";
      for (auto ode_it = (*path_it)->odes.cbegin();
           ode_it != (*path_it)->odes.cend(); ode_it++) {
        s << "(= d/dt[" << ode_it->first << "] "
          << pdrh::node_to_string_prefix(ode_it->second) << ")";
      }
      // introducing local time if defined
      // if(!timed_node_neg)
      //{
      s << "(= d/dt[local_time] 1.0)";
      //}
      s << "))" << endl;
    }
  }
  // defining the negated reachability formula
  s << "(assert (and (and " << endl;
  // defining initial states
  s << "(or ";
  for (pdrh::state st : pdrh::init) {
    if (path.front()->id == st.id) {
      s << "(" << pdrh::node_fix_index(st.prop, 0, "0") << ")";
    }
  }
  s << ")" << endl;
  // defining bounds for the parameter boxes
  for (box b : boxes) {
    std::map<string, capd::interval> m = b.get_map();
    for (int i = 0; i < path.size(); i++) {
      for (auto it = m.cbegin(); it != m.cend(); it++) {
        s << "(>= " << it->first << "_" << i << "_0 " << it->second.leftBound()
          << ")" << endl;
        s << "(<= " << it->first << "_" << i << "_0 " << it->second.rightBound()
          << ")" << endl;
        s << "(>= " << it->first << "_" << i << "_t " << it->second.leftBound()
          << ")" << endl;
        s << "(<= " << it->first << "_" << i << "_t " << it->second.rightBound()
          << ")" << endl;
      }
    }
  }
  // defining trajectory
  int step = 0;
  for (pdrh::mode* m : path) {
    // defining integrals
    s << "(= [";
    for (auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++) {
      s << ode_it->first << "_" << step << "_t ";
    }
    // defining local time if enabled
    // if((step == path.size() - 1) && (!timed_node_neg))
    // if(!timed_node_neg)
    //{
    s << "local_time_" << step << "_t";
    //}
    s << "] (integral 0.0 time_" << step << " [";
    for (auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++) {
      s << ode_it->first << "_" << step << "_0 ";
    }
    // defining local time if enabled
    // if((step == path.size() - 1) && (!timed_node_neg))
    // if(!timed_node_neg)
    //{
    s << "local_time_" << step << "_0";
    //}
    s << "] flow_" << m->id << "))" << endl;
    // defining invariants (probably not needed for the compliment formula)
    //for (pdrh::node* invt : m->invts) {
    //  s << "(forall_t " << m->id << " [0.0 time_" << step << "] "
    //    << pdrh::node_fix_index(invt, step, "t") << ")" << endl;
    //}
    // checking the current depth
    if (step < path.size() - 1) {
      // defining jumps
      for (pdrh::mode::jump j : m->jumps) {
        // cout << "Jumping from " << m->id << " to " << j.next_id << "(control
        // " << path.at(step+1)->id << ")" << endl;
        if (j.next_id == path.at(step + 1)->id) {
          // cout << "Recording the jumping from " << m->id << " to " <<
          // j.next_id << "(control " << path.at(step+1)->id << ")" << endl;
          s << pdrh::node_fix_index(j.guard, step, "t") << endl;
          if (step < path.size() - 1) {
            for (auto reset_it = j.reset.cbegin(); reset_it != j.reset.cend();
                 reset_it++) {
              s << "(= " << reset_it->first << "_" << step + 1 << "_0 "
                << pdrh::node_fix_index(reset_it->second, step, "t") << ")";
            }
          }
        }
      }
    }
    step++;
  }
  s << ")";
  // defining goal (placing the negation of all goals into conjunction)
  s << "(and ";
  for (pdrh::state st : pdrh::goal) {
    if (path.back()->id == st.id) {
      // pdrh::node* timed_node_neg = ap::get_time_node_neg(st.prop);
      // defining time vars
      vector<string> time_vars = global_config.time_var_name;
      time_vars.push_back(global_config.sample_time);
      pdrh::node* timed_node_neg =
          pdrh::get_node_neg_by_value(st.prop, time_vars);
      if (!timed_node_neg) {
        // checking if there is a not in front of the guard predicate because
        // dReal does not work nicely with double negation

        // commenting out the final local_time assertion for now
        s << "(= local_time_" << path.size() - 1 << "_t "
          << pdrh::node_fix_index(path.back()->time.second, path.size() - 1,
                                  "0")
          << ")" << endl;
        if (st.prop->value == "not") {
          s << "(forall_t " << st.id << " [0 time_" << path.size() - 1 << "] ("
            << pdrh::node_fix_index(st.prop->operands.front(), path.size() - 1,
                                    "t")
            << "))";
        }
        // transforming the negation of disjunction into the conjunction of
        // negations
        else if (st.prop->value == "or") {
          for (pdrh::node* n : st.prop->operands) {
            s << "(forall_t " << st.id << " [0 time_" << path.size() - 1
              << "] (not " << pdrh::node_fix_index(n, path.size() - 1, "t")
              << "))";
          }
        } else {
          s << "(forall_t " << st.id << " [0 time_" << path.size() - 1
            << "] (not " << pdrh::node_fix_index(st.prop, path.size() - 1, "t")
            << "))";
        }
      } else {
        s << pdrh::node_fix_index(timed_node_neg, path.size() - 1, "t");
        delete timed_node_neg;
      }
    }
  }
  s << ")))" << endl;
  // final statements
  s << "(check-sat)" << endl;
  s << "(exit)" << endl;
  return s.str();
}

string smt2_generator::reach_c_to_smt2(int depth, vector<pdrh::mode*> path,
                                       vector<box> boxes) {
  if (depth == path.size() - 1) {
    return smt2_generator::reach_c_to_smt2(path, boxes);
  } else {
    stringstream s;
    // setting logic
    s << "(set-logic QF_NRA_ODE)" << endl;
    // checking whether either of last jumps have a time node
    //        pdrh::node* timed_node_neg;
    //        for(pdrh::mode::jump j : path.at(depth)->jumps)
    //        {
    //            timed_node_neg = pdrh::get_time_node_neg(j.guard);
    //            if(timed_node_neg)
    //            {
    //                //cout << "Found timed node: " <<
    //                pdrh::node_to_string_prefix(timed_node_neg) << endl;
    //                break;
    //            }
    //        }
    // declaring variables and defining bounds
    for (auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++) {
      s << "(declare-fun " << it->first << " () Real)" << endl;
      for (int i = 0; i <= depth; i++) {
        s << "(declare-fun " << it->first << "_" << i << "_0 () Real)" << endl;
        s << "(declare-fun " << it->first << "_" << i << "_t () Real)" << endl;
        if (it->second.first->value != "-infty") {
          s << "(assert (>= " << it->first << "_" << i << "_0 "
            << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
          s << "(assert (>= " << it->first << "_" << i << "_t "
            << pdrh::node_to_string_prefix(it->second.first) << "))" << endl;
        }
        if (it->second.second->value != "infty") {
          s << "(assert (<= " << it->first << "_" << i << "_0 "
            << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
          s << "(assert (<= " << it->first << "_" << i << "_t "
            << pdrh::node_to_string_prefix(it->second.second) << "))" << endl;
        }
      }
    }
    // declaring time
    for (int i = 0; i <= depth; i++) {
      s << "(declare-fun time_" << i << " () Real)" << endl;
      s << "(assert (>= time_" << i << " "
        << pdrh::node_fix_index(path.at(i)->time.first, i, "0") << "))" << endl;
      s << "(assert (<= time_" << i << " "
        << pdrh::node_fix_index(path.at(i)->time.second, i, "0") << "))"
        << endl;
    }
    // declaring local time and bounds
    //        if (!timed_node_neg)
    //        {
    s << "(declare-fun local_time () Real)" << endl;
    // cout << "HERE" << endl;
    for (unsigned long i = 0; i < depth; i++) {
      s << "(declare-fun local_time_" << i << "_0 () Real)" << endl;
      s << "(declare-fun local_time_" << i << "_t () Real)" << endl;
      s << "(assert (= local_time_" << i << "_0 "
        << pdrh::node_fix_index(path.at(i)->time.first, i, "0") << "))" << endl;
      s << "(assert (>= local_time_" << i << "_t "
        << pdrh::node_fix_index(path.at(i)->time.first, i, "0") << "))" << endl;
      s << "(assert (<= local_time_" << i << "_t "
        << pdrh::node_fix_index(path.at(i)->time.second, i, "0") << "))"
        << endl;
    }
    // last mode
    // s << "(declare-fun local_time () Real)" << endl;
    s << "(declare-fun local_time_" << depth << "_0 () Real)" << endl;
    s << "(declare-fun local_time_" << depth << "_t () Real)" << endl;
    s << "(assert (= local_time_" << depth << "_0 "
      << pdrh::node_fix_index(path.at(depth)->time.first, depth, "0") << "))"
      << endl;
    s << "(assert (>= local_time_" << depth << "_t "
      << pdrh::node_fix_index(path.at(depth)->time.first, depth, "0") << "))"
      << endl;
    s << "(assert (<= local_time_" << depth << "_t "
      << pdrh::node_fix_index(path.at(depth)->time.second, depth, "0") << "))"
      << endl;
    //        }
    // defining odes
    int step = 0;
    for (auto path_it = path.cbegin(); path_it != path.cend(); path_it++) {
      if (std::find(path.cbegin(), path_it, *path_it) == path_it) {
        s << "(define-ode flow_" << (*path_it)->id << " (";
        for (auto ode_it = (*path_it)->odes.cbegin();
             ode_it != (*path_it)->odes.cend(); ode_it++) {
          s << "(= d/dt[" << ode_it->first << "] "
            << pdrh::node_to_string_prefix(ode_it->second) << ")";
        }
        // introducing local time if defined
        // if((!timed_node_neg))
        //{
        s << "(= d/dt[local_time] 1.0)";
        //}
        s << "))" << endl;
      }
      if (step >= depth) {
        break;
      }
      step++;
    }
    // defining the negated reachability formula
    s << "(assert (and (and " << endl;
    // defining initial states
    s << "(or ";
    for (pdrh::state st : pdrh::init) {
      if (path.front()->id == st.id) {
        s << "(" << pdrh::node_fix_index(st.prop, 0, "0") << ")";
      }
    }
    s << ")" << endl;
    // defining boxes bounds
    for (box b : boxes) {
      std::map<string, capd::interval> m = b.get_map();
      for (int i = 0; i <= depth; i++) {
        for (auto it = m.cbegin(); it != m.cend(); it++) {
          s << "(>= " << it->first << "_" << i << "_0 "
            << it->second.leftBound() << ")" << endl;
          s << "(<= " << it->first << "_" << i << "_0 "
            << it->second.rightBound() << ")" << endl;
          s << "(>= " << it->first << "_" << i << "_t "
            << it->second.leftBound() << ")" << endl;
          s << "(<= " << it->first << "_" << i << "_t "
            << it->second.rightBound() << ")" << endl;
        }
      }
    }
    // defining trajectory
    for (int i = 0; i <= depth; i++) {
      pdrh::mode* m = path.at(i);
      // defining integrals
      s << "(= [";
      for (auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++) {
        s << ode_it->first << "_" << i << "_t ";
      }
      // defining local time if enabled
      // if(!timed_node_neg)
      //{
      s << "local_time_" << i << "_t";
      //}
      s << "] (integral 0.0 time_" << i << " [";
      for (auto ode_it = m->odes.cbegin(); ode_it != m->odes.cend(); ode_it++) {
        s << ode_it->first << "_" << i << "_0 ";
      }
      // defining local time if enabled
      // if(!timed_node_neg)
      //{
      s << "local_time_" << i << "_0";
      //}
      s << "] flow_" << m->id << "))" << endl;
      // defining invariants (switched off for now)
      //for (pdrh::node* invt : m->invts) {
      //  s << "(forall_t " << m->id << " [0.0 time_" << i << "] "
      //    << pdrh::node_fix_index(invt, i, "t") << ")" << endl;
      //}
      // checking the current depth
      if (i < depth) {
        // defining jumps
        for (pdrh::mode::jump j : m->jumps) {
          // getting only the jumps leading to the next mode in the path
          if (j.next_id == path.at(i + 1)->id) {
            s << pdrh::node_fix_index(j.guard, i, "t") << endl;
            if (i < path.size() - 1) {
              for (auto reset_it = j.reset.cbegin(); reset_it != j.reset.cend();
                   reset_it++) {
                s << "(= " << reset_it->first << "_" << i + 1 << "_0 "
                  << pdrh::node_fix_index(reset_it->second, i, "t") << ")";
              }
            }
          }
        }
      }
    }
    s << ")" << endl;
    // defining the last jump
    s << "(and ";
    for (pdrh::mode::jump j : path.at(depth)->jumps) {
      if (j.next_id == path.at(depth + 1)->id) {
        // pdrh::node* timed_node_neg = ap::get_time_node_neg(j.guard);
        // extracting time variables
        vector<string> time_vars = global_config.time_var_name;
        time_vars.push_back(global_config.sample_time);
        pdrh::node* timed_node_neg =
            pdrh::get_node_neg_by_value(j.guard, time_vars);
        if (!timed_node_neg) {
          // checking if there is a not in front of the guard predicate because
          // dReal does not work nicely with double negation
          s << "(= local_time_" << depth << "_t "
            << pdrh::node_fix_index(path.at(depth)->time.second, depth, "0")
            << ")" << endl;
          if (j.guard->value == "not") {
            /*
            pdrh::node *guard_without_negation = new pdrh::node();
            pdrh::copy_tree(guard_without_negation, j.guard->operands.front());
            s << "(forall_t " << path.at(depth)->id << " [0 time_" << depth <<
            "] (" << pdrh::node_fix_index(guard_without_negation, depth, "t") <<
            "))"; delete guard_without_negation;
            */
            s << "(forall_t " << path.at(depth)->id << " [0 time_" << depth
              << "] ("
              << pdrh::node_fix_index(j.guard->operands.front(), depth, "t")
              << "))";
          }
          // transforming the negation of disjunction into the conjunction of
          // negations
          else if (j.guard->value == "or") {
            for (pdrh::node* n : j.guard->operands) {
              s << "(forall_t " << path.at(depth)->id << " [0 time_" << depth
                << "] (not " << pdrh::node_fix_index(n, depth, "t") << "))";
            }
          } else {
            s << "(forall_t " << path.at(depth)->id << " [0 time_" << depth
              << "] (not " << pdrh::node_fix_index(j.guard, depth, "t") << "))";
          }
        } else {
          s << pdrh::node_fix_index(timed_node_neg, depth, "t");
          delete timed_node_neg;
        }
      }
    }
    s << ")))" << endl;
    // asserting the time point for the last mode
    // final statements
    s << "(check-sat)" << endl;
    s << "(exit)" << endl;
    return s.str();
  }
}
