//
// Created by kny on 27/02/18.
//

#ifndef PROBREACH_TRANSLATOR_H
#define PROBREACH_TRANSLATOR_H

#include "MatlabEngine.hpp"
#include "MatlabDataArray.hpp"
#include "pdrh_config.h"
#include <pdrh.h>
#include "translator_util.h"
#include <sstream>
#include <logging/easylogging++.h>
#include <algorithm>

using namespace std;
using namespace matlab::engine;
using namespace matlab::data;

namespace translator{

    extern const string slStateBase;
    extern const string subSysHandlerBase;

    struct block_connection {
        string block_name;
        int port_id;

        block_connection(string name, int id){
          this->block_name = name;
          this->port_id = id;
        }
    };

    class Translator{
    private:
        std::unique_ptr<matlab::engine::MATLABEngine> engine;
        matlab::data::ArrayFactory arrayFactory;
        string modelName, systemHandlerName, parentChart, currentSubSystemHandler;

    public:
        Translator();

        void translate_model();

        ~Translator();

    private:
        string add_state_transition(pdrh::mode& mode);
        void add_default_transition(int start_node);
        void add_scope_block(const string& subSysHandler, const string& blkName, const unsigned long inportCount);
        string translate_jump_guard(pdrh::node* guard, int mode_id);
        string translate_reset_expression(pdrh::node* reset_expr, int mode_id);
        string translate_reset_condition(pdrh::mode::jump& jump, int source_mode_id);
        void translate_ode_expression(pdrh::node *expr, block_connection parent_block);
        void generate_init_var_blocks(const pdrh::mode &m);
        void set_system_time_interval(const string& subsys, double start_time, double end_time);
        string addBlock(string subSysHandler, string srcPath, string blkName);
        string addBlock(string subSysHandler, string srcPath, string blkName,
                      translator::block_connection &connect_to);
        void connect_blocks(string subSysHandler, block_connection out_block, block_connection in_block);
        void set_block_param(string subSysHandler, string blkName, string parameter, string value);
    };


    void translate();
    string get_initial_value(string variable_name);
    string resolve_variable_init_expr(pdrh::node *node);
    void translate_ode_expression(pdrh::node *expr);

    void translate_model();
}

#endif //PROBREACH_TRANSLATOR_H
