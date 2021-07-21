//
// Created by kny on 27/02/18.
//

#ifndef PROBREACH_TRANSLATOR_H
#define PROBREACH_TRANSLATOR_H

#include <logging/easylogging++.h>

#include <algorithm>
#include <sstream>

#include "MatlabDataArray.hpp"
#include "MatlabEngine.hpp"
#include "model.h"
#include "node.h"
#include "pdrh_config.h"
#include "translator_util.h"

using namespace std;
using namespace matlab::engine;
using namespace matlab::data;

namespace translator {

extern const string slStateBase;
extern const string subSysHandlerBase;

struct block_connection {
  string block_name;
  int port_id;

  block_connection(string name, int id) {
    this->block_name = name;
    this->port_id = id;
  }
};

class Translator {
 private:
  std::unique_ptr<matlab::engine::MATLABEngine> engine;
  matlab::data::ArrayFactory arrayFactory;
  string modelName, systemHandlerName, parentChart, currentSubSystemHandler;

  // Used for positioning blocks
  const int yIncrement = 140;
  const int xIncrement = 100;

 public:
  Translator();

  void translate_model();

  /**
   * Translates the model in two distinct subsystems: Plant and Controller
   * The aim of this translation is to have the controller logic contained
   * within a dedicated subsystem so that it can be separately compiled and
   * executed on hardware in a PIl (processor-in-the-loop) block/simulation.
   *
   * This method introduces dummy states for loop-back transitions (jumps that
   * have as destination the originating state). These dummy state incur some
   * cost on the execution speed and precision of the simulation, however,
   * testing so far shows that this can be overcome by manually selecting a
   * small-enough step size (at the expense of additional simulation time).
   *
   */
  void translate_model_decomposed();

  ~Translator();

 private:
  string add_state_transition(pdrh::mode &mode);
  void add_default_transition(int start_node);
  void add_scope_block(const string &subSysHandler, const string &blkName,
                       const unsigned long inportCount);
  string translate_jump_guard(pdrh::node *guard, int mode_id);
  string translate_reset_expression(pdrh::node *reset_expr, int mode_id);
  string translate_reset_condition(pdrh::mode::jump &jump, int source_mode_id);
  void translate_ode_expression(pdrh::node *expr,
                                block_connection parent_block);
  void generate_init_var_blocks(const pdrh::mode &m);
  string addBlock(string subSysHandler, string srcPath, string blkName);
  string addBlock(string subSysHandler, string srcPath, string blkName,
                  translator::block_connection &connect_to);
  void connect_blocks(string subSysHandler, block_connection out_block,
                      block_connection in_block);
  void set_block_param(string subSysHandler, string blkName, string parameter,
                       string value);

  void add_chart_data(string id, string scope);

  void connect_blocks(string &subSysHandler, string out_block,
                      string out_block_port_name, string dest_block,
                      string dest_block_port_name);

  string add_transition(const string &parentChartRef, const string &sourceState,
                        const string &destState, const string &label,
                        const int source_oclock = 6, const int dest_oclock = 0);

  /*
   *The methods below are all used to decompose the model by
   *translate_model_decomposed();
   * */
  void add_plant_transitions(const pdrh::mode &mode);

  void add_controller_transitions(const pdrh::mode &mode);

  string controller_jump_guard(pdrh::node *guard, int mode_id);

  string controller_reset_condition(const pdrh::mode::jump &jump,
                                    const int source_mode_id);

  string controller_reset_expression(pdrh::node *reset_expr, int mode_id);
};

void translate();
string get_initial_value(string variable_name);
string resolve_variable_init_expr(pdrh::node *node);

void translate_ode_expression(pdrh::node *expr);

void translate_model();
}  // namespace translator

#endif  // PROBREACH_TRANSLATOR_H
