//
// Created by kny on 27/02/18.
//

#include <sstream>
#include <logging/easylogging++.h>
#include <util/pdrh.h>

#include "engine.h"
#include "MatlabEngine.hpp"
#include "MatlabDataArray.hpp"
#include "translator.h"
#include "pdrh_config.h"
#include "translator_util.h"


using namespace std;
using namespace matlab::engine;
using namespace matlab::data;


//TODO: read number of jump counts from main (it's command line option)
void print_map(map<string, pair<pdrh::node*, pdrh::node*>>& map1){
    for (auto& t : map1)
        std::cout << t.first << " "
                  << t.second.first->value << " "
                  << t.second.second->value << "\n";
}

translator::Translator::Translator() {
    this->engine = startMATLAB();

    vector<string> tokenised_filepath = split(global_config.model_filename, '/');
    vector<string> filename = split(tokenised_filepath.at(tokenised_filepath.size() - 1), '.');
    cout<<global_config.model_filename<<endl;
    this->modelName = "prostate_cancer";
    this->systemHandlerName = "h";
}

void translator::Translator::set_block_param(const string subSysHandler, const string blkName,
                                             const string parameter, const string value){
    ostringstream command;
    command << "set_param(fullfile(" + subSysHandler +".Path, " << subSysHandler << ".Name, '" << blkName + "'), '"
            << parameter << "', '" << value << "');";
    this->engine->eval(convertUTF8StringToUTF16String(command.str()));
}

void translator::Translator::addBlock(string subSysHandler, string srcPath, string blkName) {
    string commandString = systemHandlerName +  " = add_block(" + srcPath + ", fullfile(" + subSysHandler +".Path, " +
            subSysHandler + ".Name, '" + blkName + "'))";
    this->engine->eval(convertUTF8StringToUTF16String(commandString));
}

void translator::Translator::addBlock(string subSysHandler, string srcPath, string blkName,
                                      translator::block_connection previous_block) {
    ostringstream add_block_command;
    add_block_command << systemHandlerName << " = add_block('" << srcPath << "', fullfile(" << subSysHandler
                      << ".Path, " << subSysHandler << ".Name, '" << blkName + "'))";

    this->engine->eval(convertUTF8StringToUTF16String(add_block_command.str()));

    ostringstream add_line_command;
    add_line_command << "add_line(fullfile(" << subSysHandler << ".Path, " << subSysHandler << ".Name), '"
                     << blkName << "/1', '" << previous_block.block_name << "/" << previous_block.port_id
                     << "', 'autorouting', 'on')";

    this->engine->eval(convertUTF8StringToUTF16String(add_line_command.str()));
}

void translator::Translator::set_system_time_interval(const string& subsys, double start_time, double end_time){
    ostringstream strs;
    strs << "set_param(";
    strs <<  subsys << ", 'StartTime', '" << start_time << "')";
    this->engine->eval(convertUTF8StringToUTF16String(strs.str()));
    strs.clear();
    strs << "set_param(";
    strs << subsys << ", 'EndTime', '" << end_time << "')";
    this->engine->eval(convertUTF8StringToUTF16String(strs.str()));
}

void translator::Translator::generate_init_var_blocks(const pdrh::mode &m){

    for(auto it = m.odes.cbegin(); it != m.odes.cend(); it++){
        string init_value = translator::get_initial_value(it->first);
        cout<< "Initialising blocks for var " << it->first;
        if (strcmp(it->second->value.c_str(), "0") == 0){
            this->addBlock(this->currentSubSystemHandler, "'simulink/Commonly Used Blocks/Constant'", it->first);
            this->set_block_param(this->currentSubSystemHandler, it->first, "Value", init_value);
        } else {
            this->addBlock(this->currentSubSystemHandler, "'simulink/Continuous/Integrator'", it->first);
            this->set_block_param(this->currentSubSystemHandler, it->first, "InitialCondition", init_value);
        }
    }
}

void translator::Translator::translate_ode_expression(pdrh::node *expr){
    cout<<"Called with value: " << expr->value << " and Operands:" << expr->operands.size()<<endl;
    if(expr->operands.size() == 0)
    {

    }
    else if(expr->operands.size() > 2)
    {
        CLOG(ERROR, "model") << "The number of operands can't be less than 2";
        exit(EXIT_FAILURE);
    }
    else
//        return 1;
    {
        if(strcmp(expr->value.c_str(), "+") == 0)
        {
            if(expr->operands.size() == 1)
            {

            }
            else if(expr->operands.size() == 2)
            {

            }
        }
        else if(strcmp(expr->value.c_str(), "-") == 0)
        {
            if(expr->operands.size() == 1)
            {
//                return translate_ode_expression(expr->operands.front());
            }
            else if(expr->operands.size() == 2)
            {
//                return translate_ode_expression(expr->operands.front()) -
//                        translate_ode_expression(expr->operands.back());
            }
        }
        else if(strcmp(expr->value.c_str(), "*") == 0)
        {
//            return node_to_interval(expr->operands.front()) *
//                    node_to_interval(expr->operands.back());
        }
        else if(strcmp(expr->value.c_str(), "/") == 0)
        {

        }
        else if(strcmp(expr->value.c_str(), "^") == 0)
        {

        }
        else if(strcmp(expr->value.c_str(), "sqrt") == 0)
        {

        }
        else if(strcmp(expr->value.c_str(), "abs") == 0)
        {

        }
        else if(strcmp(expr->value.c_str(), "exp") == 0)
        {

        }
        else if(strcmp(expr->value.c_str(), "log") == 0)
        {

        }
        else if(strcmp(expr->value.c_str(), "sin") == 0)
        {

        }
        else if(strcmp(expr->value.c_str(), "cos") == 0)
        {

        }
        else if(strcmp(expr->value.c_str(), "tan") == 0)
        {

        }
        else if(strcmp(expr->value.c_str(), "asin") == 0)
        {

        }
        else if(strcmp(expr->value.c_str(), "acos") == 0)
        {

        }
        else if(strcmp(expr->value.c_str(), "atan") == 0)
        {

        }
            // the node is a reference to a variable
        else if(pdrh::var_exists(string(expr->value.c_str()))){


        }
            // the node is a reference to a constant number, assuming 0.0 (zero) is not used in the
            // ODE expression
        else if(strtod(expr->value.c_str(), nullptr) != 0.0){

        }
        else
        {
            CLOG(ERROR, "model") << "Unknown function \"" << expr->value << "\"";
            exit(EXIT_FAILURE);
        }
    }
}

void translator::Translator::translate_model(){
    matlab::data::ArrayFactory factory;

    //TODO: bound variables in Simulink: pick initial value in range
    //TODO: non-determinism
    this->engine->eval(convertUTF8StringToUTF16String(systemHandlerName + " = new_system('" + modelName + "');"));
//    engine->eval(convertUTF8StringToUTF16String(buffer));
    this->engine->eval(convertUTF8StringToUTF16String("open_system(" + systemHandlerName + ");"));
    this->engine->eval(convertUTF8StringToUTF16String("load_system('sflib');"));
    this->engine->eval(convertUTF8StringToUTF16String("add_block('sflib/Chart', ['" + modelName + "' '/Chart']);"));
    this->engine->eval(convertUTF8StringToUTF16String("rt = sfroot;"));
    this->engine->eval(convertUTF8StringToUTF16String("m = rt.find('-isa', 'Stateflow.Machine', 'name', '" + modelName + "');"));
    this->engine->eval(convertUTF8StringToUTF16String("c = m.find('-isa', 'Stateflow.Chart');"));

    for (pdrh::mode m : pdrh::modes){
        ostringstream slState, subSysHandler;
        slState << "mode" << m.id;
        subSysHandler << "subSysHandler" << m.id;
        currentSubSystemHandler = subSysHandler.str();
        this->engine->eval(convertUTF8StringToUTF16String(slState.str() + " = Stateflow.SimulinkBasedState(c);"));
        this->engine->eval(convertUTF8StringToUTF16String(slState.str() + ".Name = '" + slState.str() + "';"));
        this->engine->eval(convertUTF8StringToUTF16String(subSysHandler.str() + " = " + slState.str() + ".getDialogProxy;"));

        this->generate_init_var_blocks(m);

        for(auto it = m.odes.cbegin(); it != m.odes.cend(); it++){

            this->translate_ode_expression(it->second);
        }
    }
}

translator::Translator::~Translator() {
  this->engine.reset();
}


void addBlock(const unique_ptr<MATLABEngine>& engine, string systemHandler, string subSysHandler, string srcPath, string blkName) {
    string commandString = systemHandler +  " = add_block('" + srcPath + "', fullfile(" + subSysHandler +".Path, " +
                           subSysHandler + ".Name, '" + blkName + "'))";
    engine->eval(convertUTF8StringToUTF16String(commandString));
}

void addBlock(const unique_ptr<MATLABEngine>& engine, string systemHandler, string subSysHandler,
              string srcPath, string blkName, translator::block_connection previous_block) {
    ostringstream add_block_command;
    add_block_command << systemHandler << " = add_block('" << srcPath << "', fullfile(" << subSysHandler
                      << ".Path, " << subSysHandler << ".Name, '" << blkName + "'))";
    engine->eval(convertUTF8StringToUTF16String(add_block_command.str()));
//    string add_line_command = "add_line(fullfile(" + subSysHandler +".Path, " +
//    subSysHandler + ".Name), '" + blkName + "/1', '" + previous_block.block_name + "/'";
    ostringstream add_line_command;
    add_line_command << "add_line(fullfile(" << subSysHandler << ".Path, " << subSysHandler << ".Name), '"
                     << blkName << "/1', '" << previous_block.block_name << "/" << previous_block.port_id
                     << "', 'autorouting', 'on')";
    engine->eval(convertUTF8StringToUTF16String(add_line_command.str()));
}

int model_creation_test(){
    // Start the Matlab Engine
    unique_ptr<MATLABEngine> engine = startMATLAB();

    matlab::data::ArrayFactory factory;

    string modelName = "testModel";
    string handlerName = "h";

    //TODO: bound variables in Simulink: pick initial value in range
    //TODO: non-determinism
    engine->eval(convertUTF8StringToUTF16String("h = new_system('testModel');"));
//    engine->eval(convertUTF8StringToUTF16String(buffer));
    engine->eval(convertUTF8StringToUTF16String("open_system(h);"));
    engine->eval(convertUTF8StringToUTF16String("load_system('sflib');"));
    engine->eval(convertUTF8StringToUTF16String("add_block('sflib/Chart', ['testModel' '/Chart']);"));
    engine->eval(convertUTF8StringToUTF16String("rt = sfroot;"));
    engine->eval(convertUTF8StringToUTF16String("m = rt.find('-isa', 'Stateflow.Machine', 'name', 'testModel');"));
    engine->eval(convertUTF8StringToUTF16String("c = m.find('-isa', 'Stateflow.Chart');"));

    engine->eval(convertUTF8StringToUTF16String("ss1 = Stateflow.SimulinkBasedState(c);"));
    engine->eval(convertUTF8StringToUTF16String("ss1.Name = 'Gain1';"));
    engine->eval(convertUTF8StringToUTF16String("subsysH = ss1.getDialogProxy;"));

    //TODO: enum or case-switch
    addBlock(engine, "h", "subsysH", "built-in/inport", "in");
    addBlock(engine, "h", "subsysH", "built-in/outport", "out");
    addBlock(engine, "h", "subsysH", "built-in/gain", "K", translator::block_connection("out", 1));

//    set_system_time_interval(engine, "subsysH.Name", 0, 2000.0);

//    engine->eval(convertUTF8StringToUTF16String("Simulink.BlockDiagram.arrangeSystem(subsysH)"));

    engine->eval(convertUTF8StringToUTF16String("save_system('testModel')"));

    matlab::data::Array subsysH = engine->getVariable(convertUTF8StringToUTF16String("subsysH"));
    Array systemHandler = engine->getVariable(convertUTF8StringToUTF16String("h"));

    ArrayType subsysArrType = subsysH.getType();

    matlab::data::Array ss1Handler = engine->getVariable(convertUTF8StringToUTF16String("ss1"));
    matlab::data::CharArray ss1Name = engine->getProperty(ss1Handler, convertUTF8StringToUTF16String("Name"));

    cout<<"Stateflow state name: " + ss1Name.toAscii()<<endl;


    cout<<"Added block"<<endl;

//    engine->eval(convertUTF8StringToUTF16String("figureHandle = figure;"));
//    cout<<"Created system handler"<<endl;
//
//    matlab::data::Array systemHandler = engine->
//            getVariable(convertUTF8StringToUTF16String("figureHandle"));
//
//    matlab::data::CharArray units = engine->
//            getProperty(systemHandler, convertUTF8StringToUTF16String("Units"));
//
//    // Display property value
//    cout << "Units property: " << units.toAscii() << std::endl;


    return 0;
}

string translator::get_initial_value(string variable_name){
    for(pdrh::state s : pdrh::init){
        for(pdrh::node* node : s.prop->operands){
            if (strcmp(node->value.c_str(), "=") == 0){
                if (variable_name.compare(node->operands.at(0)->value) == 0){
                    return node->operands.at(1)->value;
                }
            }
            // DUMMY VALUE 5
            else return "5";
            }
        }
}

void translator::parse_tree(){
    cout<<pdrh::model_to_string();
    print_map(pdrh::var_map);
    print_map(pdrh::par_map);
//    model_creation_test();

    translator::Translator *translator1 = new Translator();
    translator1->translate_model();

    cout<<"Test complete"<<endl;
    cout<<translator::get_initial_value("y");
    delete translator1;
//    test_engine_call();
}


//double translator::test_engine_call() {
//    // Create arrays of Matlab type
//    mxArray *X = mxCreateDoubleMatrix(1, 1, mxREAL);
//    mxArray *Y = mxCreateDoubleMatrix(1, 1, mxREAL);
//
//    // Matlab arrays --> double arrays
//    double *ptrToMatX = reinterpret_cast<double *>(mxGetData(X));
//    double *ptrToMatY = reinterpret_cast<double *>(mxGetData(Y));
//
//    // Manipulate ordinary c++ arrays
//    ptrToMatX[0] = 1;
//    ptrToMatY[0] = 2;
//
//    // Start the Matlab Engine
//    engine *ep;
//    if (!(ep = engOpen("\0"))) {
//        fprintf(stderr, "\nCan't start MATLAB engine\n");
//        return 0;
//    }
//
//    // Copy the variables into Matlab prompt
//    engPutVariable(ep, "X", X);
//    engPutVariable(ep, "Y", Y);
//
//    // Call the function
//    engEvalString(ep, "Z = (X + Y^2)");
//
//    // Copy the variable from Matlab prompt to our code
//    mxArray *Z = engGetVariable(ep, "Z");
//
//    // Convert this variable to ordinary c++ array and show it
//    double *ptrToMatZ = reinterpret_cast<double *>(mxGetData(Z));
//    std::cout << "result is " << *ptrToMatZ << std::endl;
//
//    return *ptrToMatZ;
//}

