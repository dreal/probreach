//
// Created by fedor on 26/02/16.
//

#include <unistd.h>
#include <omp.h>
#include "smt2_generator.h"
#include "decision_procedure.h"
#include "dreal_wrapper.h"
#include "pdrh_config.h"

using namespace std;

/**
 * Evaluates reachability for a set of paths and parameter boxes.
 *
 * @param paths - set of paths to evaluate.
 * @param boxes - set of parameter boxes to evaluate.
 * @param solver_bin - full path to solver binary.
 * @param solver_opt - string of solver options.
 * @return satisfiability of reachability for the given set of paths and parameter boxes.
 */
int decision_procedure::evaluate(
  vector<vector<pdrh::mode *>> paths,
  vector<box> boxes,
  string solver_bin,
  string solver_opt)
{
  int undet_counter = 0;
  for (vector<pdrh::mode *> path : paths)
  {
    //        stringstream s;
    //        for(pdrh::mode* m : path) s << m->id << " ";
    int res = evaluate(path, boxes, solver_bin, solver_opt);
    if (res == decision_procedure::result::SAT)
    {
      return res;
    }
    else if (res == decision_procedure::result::UNDET)
    {
      undet_counter++;
    }
  }
  if (undet_counter > 0)
  {
    return decision_procedure::result::UNDET;
  }
  return decision_procedure::result::UNSAT;
}

/**
 * Evaluates reachability for a path and a set of parameter boxes.
 *
 * @param path - path to evaluate.
 * @param boxes - set of parameter boxes to evaluate.
 * @param solver_bin - full path to solver binary.
 * @param solver_opt - string of solver options.
 * @return satisfiability of reachability for the given path and parameter boxes.
 */
int decision_procedure::evaluate(
  vector<pdrh::mode *> path,
  vector<box> boxes,
  string solver_bin,
  string solver_opt)
{
  // evaluating the delta-sat formula
  int first_res = decision_procedure::evaluate_delta_sat(
    path, boxes, global_config.solver_bin, solver_opt);
  if (first_res == decision_procedure::result::UNSAT)
  {
    return decision_procedure::result::UNSAT;
  }
  else if (first_res == decision_procedure::result::SAT)
  {
    // evaluating complement
    int second_res = decision_procedure::evaluate_complement(
      path, boxes, solver_bin, solver_opt);
    if (second_res == decision_procedure::result::UNSAT)
    {
      return decision_procedure::result::SAT;
    }
    else if (second_res == decision_procedure::result::SAT)
    {
      return decision_procedure::result::UNDET;
    }
  }
}

/**
 * Evaluates delta-reachability for a path and a set of parameter boxes.
 *
 * @param path - path to evaluate.
 * @param boxes - set of parameter boxes to evaluate.
 * @param solver_bin - full path to solver binary.
 * @param solver_opt - string of solver options.
 * @return delta-satisfiability of reachability for the given path and parameter boxes.
 */
int decision_procedure::evaluate_delta_sat(
  vector<pdrh::mode *> path,
  vector<box> boxes,
  string solver_bin,
  string solver_opt)
{
  // default value for the thread number
  int thread_num = 0;
#ifdef _OPENMP
  thread_num = omp_get_thread_num();
#endif
  // getting raw filename here
  std::string filename = std::string(global_config.model_filename);
  size_t ext_index = filename.find_last_of('.');
  std::string raw_filename = filename.substr(0, ext_index);
  // creating a name for the smt2 file
  std::stringstream f_stream;
  f_stream << raw_filename << "_" << path.size() - 1 << "_0_" << thread_num
           << ".smt2";
  std::string smt_filename = f_stream.str();
  // writing to the file
  std::ofstream smt_file;

  smt_file.open(smt_filename.c_str());
  // will work for one initial and one state only
  //    smt_file << pdrh2box::reach_to_smt2(pdrh::init.front(), pdrh::goal.front(), path, boxes);
  smt_file << smt2_generator::reach_to_smt2(path, boxes);
  smt_file.close();
  //    cout << pdrh2box::reach_to_smt2(pdrh::init.front(), pdrh::goal.front(), path, boxes) << endl;
  //    exit(EXIT_SUCCESS);

  if (global_config.debug)
  {
    cout << "Thread: " << omp_get_thread_num() << endl;
    cout << "First formula:" << endl;
    cout << smt2_generator::reach_to_smt2(path, boxes) << endl;
  }

  //    cout << "Solver options: " << solver_opt << endl;
  // calling dreal here
  // solver_opt.append(" --model");
  int first_res = dreal::execute(solver_bin, smt_filename, solver_opt);

  if (first_res == -1)
  {
    return decision_procedure::ERROR;
  }
  else if (first_res == 1)
  {
    if (
      (std::remove(smt_filename.c_str()) == 0) &&
      (std::remove(std::string(smt_filename + ".output").c_str()) == 0))
    {
      //LOG(DEBUG) << "Removed auxiliary files";
      return decision_procedure::UNSAT;
    }
    else
    {
      cerr << "Problem occurred while removing one of auxiliary files (UNSAT)";
      return decision_procedure::ERROR;
    }
  }
  else
  {
    if (
      (std::remove(smt_filename.c_str()) == 0) &&
      (std::remove(std::string(smt_filename + ".output").c_str()) == 0))
    {
      //            box b = dreal::parse_model(string(smt_filename + ".model"));
      //            cout << "Solution box: " << b << endl;
      //            std::remove(string(smt_filename + ".model").c_str());
      //            map<string, pdrh::node*> reset_map = pdrh::modes.front().jumps.front().reset;
      //            map<string, capd::interval> init_map;
      //            for(auto it = reset_map.begin(); it != reset_map.end(); it++)
      //            {
      //                init_map.insert(make_pair(it->first, pdrh::node_to_interval(it->second, b)));
      //            }
      //            box init_box(init_map);
      //            cout << "New init box: " << init_box << endl;
      //            pdrh::state new_init_state;
      //            new_init_state.id = pdrh::modes.front().jumps.front().next_id;
      //            new_init_state.prop = pdrh::box_to_node(init_box);
      //            cout << "New init state: " << new_init_state.id << ": " << pdrh::node_to_string_prefix(new_init_state.prop) << endl;
      //LOG(DEBUG) << "Removed auxiliary files";
      return decision_procedure::SAT;
    }
    else
    {
      cerr
        << "Problem occurred while removing one of auxiliary files (DELTA-SAT)";
      return decision_procedure::ERROR;
    }
  }
}

/**
 * Evaluates delta-non-reachability for a path and a set of parameter boxes.
 *
 * @param path - path to evaluate.
 * @param boxes - set of parameter boxes to evaluate.
 * @param solver_bin - full path to solver binary.
 * @param solver_opt - string of solver options.
 * @return delta-satisfiability of non-reachability for the given path and parameter boxes.
 */
int decision_procedure::evaluate_complement(
  vector<pdrh::mode *> path,
  vector<box> boxes,
  string solver_bin,
  string solver_opt)
{
  int thread_num = 0;
#ifdef _OPENMP
  thread_num = omp_get_thread_num();
#endif
  // getting raw filename here
  string filename = string(global_config.model_filename);
  size_t ext_index = filename.find_last_of('.');
  string raw_filename = filename.substr(0, ext_index);
  // creating a name for the smt2 file
  stringstream f_stream;
  for (int i = 0; i < path.size(); i++)
  {
    // the complement formula
    f_stream.str("");
    f_stream << raw_filename << "_" << i << "_" << path.size() - 1 << "_0_"
             << thread_num << ".c.smt2";
    string smt_c_filename = f_stream.str();
    // writing to the file
    ofstream smt_c_file;
    smt_c_file.open(smt_c_filename.c_str());
    smt_c_file << smt2_generator::reach_c_to_smt2(i, path, boxes);
    //        cout << pdrh2box::reach_c_to_smt2(i, path, boxes) << endl;
    //        exit(EXIT_SUCCESS);
    if (global_config.debug)
    {
      cout << "Thread: " << omp_get_thread_num() << endl;
      cout << "Second formula (" << i << "):" << endl;
      cout << smt2_generator::reach_c_to_smt2(i, path, boxes) << endl;
    }
    smt_c_file.close();
    // calling dreal here
    int second_res = dreal::execute(solver_bin, smt_c_filename, solver_opt);
    if (second_res == -1)
    {
      return decision_procedure::ERROR;
    }
    else if (second_res == 1)
    {
      if (
        (remove(smt_c_filename.c_str()) != 0) ||
        (remove(std::string(smt_c_filename + ".output").c_str()) != 0))
      {
        return decision_procedure::ERROR;
      }
    }
    else
    {
      if (
        (remove(smt_c_filename.c_str()) != 0) ||
        (remove(std::string(smt_c_filename + ".output").c_str()) != 0))
      {
        return decision_procedure::ERROR;
      }
      else
      {
        return decision_procedure::SAT;
      }
    }
  }
  return decision_procedure::UNSAT;
}

/**
 * Checks mode invariants given an initial state, set of parameter boxes and a time bound.
 *
 * @param m - mode.
 * @param time - time bound.
 * @param init - initial value.
 * @param boxes - set of parameter boxes.
 * @param solver_bin - full path to solver binary.
 * @param solver_opt - string of solver options.
 * @return invariants satisfiability.
 */
int decision_procedure::check_invariants(
  pdrh::mode *m,
  capd::interval time,
  box init,
  vector<box> boxes,
  string solver_bin,
  string solver_opt)
{
  // if no invariants are defined then return SAT
  if (m->invts.size() == 0)
    return decision_procedure::SAT;
  //cout << "Here!!!" << endl;
  // default value for the thread number
  int thread_num = 0;
#ifdef _OPENMP
  thread_num = omp_get_thread_num();
#endif
  // getting raw filename here
  std::string filename = std::string(global_config.model_filename);
  size_t ext_index = filename.find_last_of('.');
  std::string raw_filename = filename.substr(0, ext_index);
  // creating a name for the smt2 file
  std::stringstream f_stream;
  int res;
  std::ofstream smt_file;
  std::string smt_filename;

  // Complement formula
  f_stream.str("");
  f_stream << raw_filename << "_0_0_" << thread_num << "_c.smt2";
  smt_filename = f_stream.str();

  smt_file.open(smt_filename.c_str());
  // will work for one initial and one state only
  smt_file << smt2_generator::generate_flow_invt_check_c(m, time, init, boxes);
  smt_file.close();

  // calling dreal here
  // solver_opt.append(" --model");
  res = dreal::execute(solver_bin, smt_filename, solver_opt);
  // removing all generated files
  std::remove(smt_filename.c_str());
  std::remove(std::string(smt_filename + ".output").c_str());
  std::remove(std::string(smt_filename + ".model").c_str());
  // the result is unsat. Thus, no need for the second formula
  if (res == 1)
  {
    return decision_procedure::SAT;
  }

  // Exists for all formula
  f_stream.str("");
  f_stream << raw_filename << "_0_0_" << thread_num << ".smt2";
  smt_filename = f_stream.str();

  smt_file.open(smt_filename.c_str());
  // will work for one initial and one state only
  smt_file << smt2_generator::generate_flow_invt_check(m, time, init, boxes);
  smt_file.close();

  // calling dreal here
  solver_opt.append(" --model");
  res = dreal::execute(solver_bin, smt_filename, solver_opt);
  // removing all generated files
  std::remove(smt_filename.c_str());
  std::remove(std::string(smt_filename + ".output").c_str());
  std::remove(std::string(smt_filename + ".model").c_str());
  // the result is unsat. Thus, no need for the second formula
  if (res == 1)
  {
    return decision_procedure::UNSAT;
  }

  return decision_procedure::UNDET;
}

/**
 * Computes the time of the given jump from the current mode for a given initial value and a set of parameter boxes.
 *
 * @param m - mode.
 * @param jump - jump to take place.
 * @param init - initial value.
 * @param boxes - set of parameter boxes.
 * @return time when the given jump occurs.
 */
pair<capd::interval, box> decision_procedure::get_jump_time(
  pdrh::mode *m,
  pdrh::mode::jump jump,
  box init,
  vector<box> boxes)
{
  // default value for the thread number
  int thread_num = 0;
#ifdef _OPENMP
  thread_num = omp_get_thread_num();
#endif
  // getting raw filename here
  std::string filename = std::string(global_config.model_filename);
  size_t ext_index = filename.find_last_of('.');
  std::string raw_filename = filename.substr(0, ext_index);
  // creating a name for the smt2 file
  std::stringstream f_stream;
  int res;
  std::ofstream smt_file;
  std::string smt_filename;

  f_stream.str("");
  f_stream << raw_filename << "_0_0_" << thread_num << ".smt2";
  smt_filename = f_stream.str();

  smt_file.open(smt_filename.c_str());
  // will work for one initial and one state only
  smt_file << smt2_generator::generate_jump_check(m, {jump}, init, boxes);
  smt_file.close();

  // calling dreal here
  //global_config.solver_opt.append(" --model");
  res = dreal::execute(
    global_config.solver_bin,
    smt_filename,
    global_config.solver_opt + " --model ");
  capd::interval jump_time(-1);
  box sol_box;
  if (res == 0)
  {
    sol_box = dreal::parse_model(string(smt_filename + ".model"));
    //cout << "Witness produced by the solver: " << sol_box << endl;
    jump_time = sol_box.get_map()["time"];
  }
  // removing all generated files
  std::remove(smt_filename.c_str());
  std::remove(std::string(smt_filename + ".output").c_str());
  std::remove(std::string(smt_filename + ".model").c_str());
  map<string, capd::interval> sol_map = sol_box.get_map();
  for (box b : boxes)
  {
    map<string, capd::interval> b_map = b.get_map();
    for (auto it = b_map.begin(); it != b_map.end(); it++)
    {
      sol_box.erase(it->first);
    }
  }
  sol_box.erase("time");
  sol_box.erase("time_mock");
  return make_pair(jump_time, sol_box);
}
