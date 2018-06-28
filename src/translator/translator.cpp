//
// Created by kny on 27/02/18.
//

#include "translator.h"


using namespace std;
using namespace matlab::engine;
using namespace matlab::data;

const string translator::slStateBase = "mode";
const string translator::subSysHandlerBase = "subSysHandler";

/**
 * Initialises translator paremeters and parses model name so that is is compliant with
 * MATLAB syntax.
 */
translator::Translator::Translator() {
    cout<< "Starting MATLAB engine" << endl;

    this->engine = matlab::engine::startMATLAB();

    cout<< "MATLAB engine started" << endl;

    vector<string> tokenised_filepath = split(global_config.model_filename, '/');
    vector<string> filename = split(tokenised_filepath.at(tokenised_filepath.size() - 1), '.');
    this->modelName = filename.front();

    // replace all dashes contained within the name file with underscores
    std::replace(this->modelName.begin(), this->modelName.end(), '-', '_');

    this->systemHandlerName = "h";
    this->parentChart = "c";
}

translator::Translator::~Translator() {
    this->engine.reset();
}

/**
 * A wrapper for setting block paremeters, assumes the block already exists in the workspace, else a
 * MATLAB exception is thrown.
 * @param subSysHandler - handle to state
 * @param blkName
 * @param parameter - parameter name
 * @param value - the desired value
 */
void translator::Translator::set_block_param(const string subSysHandler, const string blkName,
                                             const string parameter, const string value){
    ostringstream command;
    command << "set_param(fullfile(" + subSysHandler +".Path, " << subSysHandler << ".Name, '" << blkName + "'), '"
            << parameter << "', '" << value << "');";
    this->engine->eval(convertUTF8StringToUTF16String(command.str()));
}

/**
 * Adds a block to the currently open canvas (defined by the value of \param subSysHandler). \param blkName and
 * \param srcPath refer to block name and its location in the default Simulink block library, respectively.
 * @param subSysHandler - handle to subsystem/state
 * @param srcPath - blocks path in standard library
 * @param blkName - block's name
 * @return - block name as it appears in MATLAB environment
 */
string translator::Translator::addBlock(string subSysHandler, string srcPath, string blkName) {
    ostringstream add_block_command;
    add_block_command << systemHandlerName << " = add_block('" << srcPath << "', fullfile(" << subSysHandler
                      << ".Path, " << subSysHandler << ".Name, '" << blkName + "'), 'MakeNameUnique', 'On');";

    this->engine->eval(convertUTF8StringToUTF16String(add_block_command.str()));

    engine->eval(convertUTF8StringToUTF16String("block_name = get_param(h, 'Name');"));
    matlab::data::CharArray blockName = engine->getVariable(convertUTF8StringToUTF16String("block_name"));
    return blockName.toAscii();
}

/**
 * Adds a block to the currently open canvas (defined by the value of \param subSysHandler). \param blkName and
 * \param srcPath refer to block name and its location in the default Simulink block library, respectively.
 * \param connect_to specifies to which block to connect the output of the newly added block, assumes this block is already
 * present on the canvas.
 * @param subSysHandler - handle to subsystem/state
 * @param srcPath - blocks path in standard library
 * @param blkName - block's name
 * @param connect_to
 * @return block name as it appears in MATLAB environment
 */
string translator::Translator::addBlock(string subSysHandler, string srcPath, string blkName,
                                      translator::block_connection &connect_to) {
    string added_block_name = addBlock(subSysHandler, srcPath, blkName);
    ostringstream add_line_command;
    add_line_command << "add_line(fullfile(" << subSysHandler << ".Path, " << subSysHandler << ".Name), '"
                     << added_block_name << "/1', '" << connect_to.block_name << "/" << connect_to.port_id
                     << "', 'autorouting', 'smart');";

    this->engine->eval(convertUTF8StringToUTF16String(add_line_command.str()));

    return added_block_name;
}

/**
 * Adds a scope block with the specified number of input ports.
 * @param subSysHandler - handle to subsystem/state
 * @param blkName
 * @param inportCount
 */
void translator::Translator::add_scope_block(const string& subSysHandler, const string& blkName, const unsigned long inportCount){
    this->addBlock(this->currentSubSystemHandler, "simulink/Sinks/Scope", blkName);
    stringstream configCommand;
    configCommand << "scopeConfig = get_param(fullfile(" << subSysHandler << ".Path, " << subSysHandler << ".Name, '"
            << blkName <<"'), 'ScopeConfiguration');" << endl;
//            << "scopeConfig.OpenAtSimulationStart = true;" <<endl
//            << "scopeConfig.NumInputPorts = '" << to_string(inportCount) << "';";
    this->engine->eval(convertUTF8StringToUTF16String(configCommand.str()));
    this->engine->eval(convertUTF8StringToUTF16String("scopeConfig.OpenAtSimulationStart = true;"));
    this->engine->eval(convertUTF8StringToUTF16String("scopeConfig.NumInputPorts = '" + to_string(inportCount) + "';"));
};

/**
 * Connects any two blocks and automatically routes the line.
 * @param subSysHandler - handle to subsystem/state
 * @param out_block - source block
 * @param in_block - destination block
 */
void translator::Translator::connect_blocks(string subSysHandler, translator::block_connection out_block,
                                            translator::block_connection in_block) {
    ostringstream add_line_command;
    add_line_command << "add_line(fullfile(" << subSysHandler << ".Path, " << subSysHandler << ".Name), '"
                     << out_block.block_name << "/" << out_block.port_id << "', '"
                     << in_block.block_name << "/" << in_block.port_id
                     << "', 'autorouting', 'smart');";
    this->engine->eval(convertUTF8StringToUTF16String(add_line_command.str()));
}

/**
 * Connects any two blocks and automatically routes the line.
 * @param subSysHandler - handle to subsystem/state
 * @param out_block - name of the root of the line
 * @param out_block_port_name - specific port of the root block
 * @param dest_block - name of the destination of the line
 * @param dest_block_port_name - specific port of the destination block
 */
void translator::Translator::connect_blocks(string &subSysHandler, string out_block, string out_block_port_name,
                                            string dest_block, string dest_block_port_name) {
    ostringstream add_line_command;
    add_line_command << "add_line(fullfile(" << subSysHandler << ".Path, " << subSysHandler << ".Name), '"
                     << out_block << "/" << out_block_port_name << "', '"
                     << dest_block << "/" << dest_block_port_name
                     << "', 'autorouting', 'smart');";
    this->engine->eval(convertUTF8StringToUTF16String(add_line_command.str()));
}

void translator::Translator::generate_init_var_blocks(const pdrh::mode &m){

    for(auto it = m.odes.cbegin(); it != m.odes.cend(); it++){
        CLOG_IF(global_config.verbose, INFO, "translator") <<  "Initialing integrator block " << it->first;
        string init_value = translator::get_initial_value(it->first);
        if (strcmp(it->second->value.c_str(), "0") == 0){
            this->addBlock(this->currentSubSystemHandler, "simulink/Continuous/Integrator", it->first);
            this->set_block_param(this->currentSubSystemHandler, it->first, "InitialCondition", init_value);
            this->set_block_param(this->currentSubSystemHandler, it->first, "ContinuousStateAttributes", "''" + it->first + "''");
        } else {
            this->addBlock(this->currentSubSystemHandler, "simulink/Continuous/Integrator", it->first);
            this->set_block_param(this->currentSubSystemHandler, it->first, "InitialCondition", init_value);
            this->set_block_param(this->currentSubSystemHandler, it->first, "ContinuousStateAttributes", "''" + it->first + "''");
        }
    }
}

/**
 * Recursively traverses an ODE expression tree and translates it in Simulink using the available
 * standard block library. \param parent_block specifies the block to which the output of the newly added block is to be
 * connected.
 * @param expr - reference to an expression node
 * @param parent_block
 */
void translator::Translator::translate_ode_expression(pdrh::node *expr, block_connection parent_block) {
//    cout<< "ODE translation: value: " << expr->value << " and " << expr->operands.size() << " operands." << endl;
    if(expr->operands.size() == 0)
    {
        // the node is a reference to a variable
        if(pdrh::var_exists(expr->value))
        {
//            cout<< "Connect " << expr->value << " to already defined variable: " << parent_block.block_name
//                << " " << parent_block.port_id <<endl;
            connect_blocks(this->currentSubSystemHandler, block_connection(expr->value, 1), parent_block);
        }
        // the node is a reference to a constant number
        else
        {
            string blkName = "Const_" + expr->value;
            string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Commonly Used Blocks/Constant", blkName, parent_block);
            set_block_param(this->currentSubSystemHandler, simulink_name, "Value", expr->value);
        }

    }
    else if(expr->operands.size() > 2)
    {
        CLOG(ERROR, "translator") << "The number of operands for operation " << expr->value << " can't be greater than 2";
        exit(EXIT_FAILURE);
    }
    else
    {
        string blkNameSuffix;
        if (expr->operands.size() == 1){
            blkNameSuffix = expr->operands.at(0)->value.compare("/") != 0 ? expr->operands.at(0)->value + "__":"div__";
        } else {
            blkNameSuffix = expr->operands.at(0)->value.compare("/") != 0 ? expr->operands.at(0)->value:"div";
            blkNameSuffix = blkNameSuffix + "_" +
                            (expr->operands.at(1)->value.compare("/") != 0 ? expr->operands.at(1)->value + "__":"div__");
        }

        if(strcmp(expr->value.c_str(), "+") == 0)
        {
            string blkName = "Add_" + blkNameSuffix;
            string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Add", blkName, parent_block);

            translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));
            translate_ode_expression(expr->operands.at(1), block_connection(simulink_name, 2));
        }
        else if(strcmp(expr->value.c_str(), "-") == 0)
        {
            if(expr->operands.size() == 1)
            {
                string blkName = "UnaryMinus_" + blkNameSuffix;
                string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Unary Minus", blkName, parent_block);

                translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));
            }
            else if(expr->operands.size() == 2)
            {
                string blkName = "Subtract_" + blkNameSuffix;
                string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Subtract", blkName, parent_block);

                translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));
                translate_ode_expression(expr->operands.at(1), block_connection(simulink_name, 2));
            }
        }
        else if(strcmp(expr->value.c_str(), "*") == 0)
        {
            string blkName = "Product_" + blkNameSuffix;
            string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Product", blkName, parent_block);

            translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));
            translate_ode_expression(expr->operands.at(1), block_connection(simulink_name, 2));
        }
        else if(strcmp(expr->value.c_str(), "/") == 0)
        {
            string blkName = "Divide_" + blkNameSuffix;
            string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Divide", blkName, parent_block);

            translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));
            translate_ode_expression(expr->operands.at(1), block_connection(simulink_name, 2));
        }
        else if(strcmp(expr->value.c_str(), "^") == 0)
        {
            string blkName = "Power_" + blkNameSuffix;
            string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Math Function", blkName, parent_block);
            set_block_param(this->currentSubSystemHandler, simulink_name, "Operator", "pow");

            translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));
            translate_ode_expression(expr->operands.at(1), block_connection(simulink_name, 2));
        }
        else if(strcmp(expr->value.c_str(), "sqrt") == 0)
        {
            string blkName = "Sqrt_" + blkNameSuffix;
            string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Sqrt", blkName, parent_block);

            translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));
        }
        else if(strcmp(expr->value.c_str(), "abs") == 0)
        {
            string blkName = "Abs_" + blkNameSuffix;
            string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Abs", blkName, parent_block);

            translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));
        }
        else if(strcmp(expr->value.c_str(), "exp") == 0)
        {
            string blkName = "Exp_" + blkNameSuffix;
            string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Math Function", blkName, parent_block);

            translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));
        }
        else if(strcmp(expr->value.c_str(), "log") == 0)
        {
            string blkName = "Log_" + blkNameSuffix;
            string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Math Function", blkName, parent_block);
            set_block_param(this->currentSubSystemHandler, simulink_name, "Operator", "log");

            translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));

        }
        else if(strcmp(expr->value.c_str(), "sin") == 0)
        {
            string blkName = "Sin_" + blkNameSuffix;
            string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Trigonometric Function", blkName, parent_block);
            set_block_param(this->currentSubSystemHandler, simulink_name, "Operator", "sin");

            translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));
        }
        else if(strcmp(expr->value.c_str(), "cos") == 0)
        {
            string blkName = "Cos_" + blkNameSuffix;
            string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Trigonometric Function", blkName, parent_block);
            set_block_param(this->currentSubSystemHandler, simulink_name, "Operator", "cos");

            translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));
        }
        else if(strcmp(expr->value.c_str(), "tan") == 0)
        {
            string blkName = "Tan_" + blkNameSuffix;
            string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Trigonometric Function",
                                            blkName, parent_block);
            set_block_param(this->currentSubSystemHandler, simulink_name, "Operator", "tan");

            translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));
        }
        else if(strcmp(expr->value.c_str(), "asin") == 0)
        {
            string blkName = "Asin_" + blkNameSuffix;
            string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Trigonometric Function", blkName, parent_block);
            set_block_param(this->currentSubSystemHandler, simulink_name, "Operator", "asin");

            translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));
        }
        else if(strcmp(expr->value.c_str(), "acos") == 0)
        {
            string blkName = "Acos_" + blkNameSuffix;
            string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Trigonometric Function", blkName, parent_block);
            set_block_param(this->currentSubSystemHandler, simulink_name, "Operator", "acos");

            translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));
        }
        else if(strcmp(expr->value.c_str(), "atan") == 0)
        {
            string blkName = "Atan_" + blkNameSuffix;
            string simulink_name = addBlock(this->currentSubSystemHandler, "simulink/Math Operations/Trigonometric Function", blkName, parent_block);
            set_block_param(this->currentSubSystemHandler, simulink_name, "Operator", "atan");

            translate_ode_expression(expr->operands.at(0), block_connection(simulink_name, 1));
        }
        else
        {
            CLOG(ERROR, "translator") << "Unknown function \"" << expr->value << "\"";
            exit(EXIT_FAILURE);
        }
    }
}

/**
 * Translates a node expression to a stateflow jump condition. Converts the expression tree to infix notation and
 * peforms substitution of logical operators.
 * @param guard
 * @param mode_id
 * @return Stateflow jump guard string
 */
string translator::Translator::translate_jump_guard(pdrh::node *guard, int mode_id)
{
    stringstream s, value;
    if (pdrh::var_map.count(guard->value)){
        value << slStateBase << mode_id << "." << guard->value;
    } else if (guard->value == "="){
        value << "==";
    } else if (guard->value == "and"){
        if (guard->operands.size() == 1){
            translate_jump_guard(guard->operands.front(), mode_id);
        } else {
            value << " & ";
        }
    } else if (guard->value == "or"){
        value << " | ";
    }
    else {
        value << guard->value;
    }
    // checking whether it is an operation node
    if(guard->operands.size() > 1)

    {
        s << "(";
        for(int i = 0; i < guard->operands.size() - 1; i++)
        {
            s << translate_jump_guard(guard->operands.at(i), mode_id);
            s << value.str();

        }
        s << translate_jump_guard(guard->operands.at(guard->operands.size() - 1), mode_id) << ")";
    }
    else if(guard->operands.size() == 1)
    {
        if(value.str() ==  "-")
        {
            s << "(" << value.str() << translate_jump_guard(guard->operands.front(), mode_id) << ")";
        }
        else
        {
            s << value.str() << "(" << translate_jump_guard(guard->operands.front(), mode_id) << ")";
        }
    }
    else
    {
        s << value.str();
    }
    return s.str();
}

/**
 * Builds all transitions from a given Stateflow state. This involves the translation of
 * jump guards and reset conditions.
 * @param mode - source mode
 * @return
 */
string translator::Translator::add_state_transition(pdrh::mode &mode){
    stringstream slSourceState;
    slSourceState << slStateBase << mode.id;
    for (pdrh::mode::jump jump : mode.jumps){
        stringstream slDestState;
        slDestState << slStateBase << jump.next_id;
        CLOG_IF(global_config.verbose, INFO, "translator") << "Adding transition to mode " << jump.next_id << ":";
        /**
         * transition_new = Stateflow.Transition(c);
           transition_new.Source = ss1;
           transition_new.Destination = ss2;
         */
        this->engine->eval(convertUTF8StringToUTF16String("new_transition = Stateflow.Transition(" + parentChart + ");"));
        this->engine->eval(convertUTF8StringToUTF16String("new_transition.Source = " + slSourceState.str() + ";"));
        this->engine->eval(convertUTF8StringToUTF16String("new_transition.Destination = " + slDestState.str() + ";"));
        this->engine->eval(convertUTF8StringToUTF16String("new_transition.SourceOClock = 6;"));
        this->engine->eval(convertUTF8StringToUTF16String("new_transition.DestinationOClock = 0;"));

        stringstream transition_label;
        transition_label << "'[" << translate_jump_guard(jump.guard, mode.id)
                         << "]{" << translate_reset_condition(jump, mode.id) << "}'";
        this->engine->eval(convertUTF8StringToUTF16String("new_transition.LabelString = " + transition_label.str() + ";"));

        CLOG_IF(global_config.verbose, INFO, "translator") << "Jump guard: " << translate_jump_guard(jump.guard, mode.id)<<endl;
        CLOG_IF(global_config.verbose, INFO, "translator") << "Jump resets: " << translate_reset_condition(jump, mode.id)<<endl;
    }
    return "new_transition";
};

/**
 * The main driver method for translating a hybrid model. Configures the environment and oversees each translation step.
 * 1 -> Initialise Simulink model file.
 * 2 -> For each mode:
 *      - initialise variables
 *      - translate ODEs
 *      - translate transitions
 * 3 -> Add default transitions
 * 4 -> Set simulation time
 */
void translator::Translator::translate_model(){
    matlab::data::ArrayFactory factory;
    int xStatePosition = 40;
    int yStatePosition = 120;
    const int yIncrement = 140;
    const int xIncrement = 100;

    /**
     * Setup the system environment
     */
    this->engine->eval(convertUTF8StringToUTF16String("mdlName = '" + modelName + "'"));
    this->engine->eval(convertUTF8StringToUTF16String(systemHandlerName + " = new_system('" + modelName + "');"));
    this->engine->eval(convertUTF8StringToUTF16String("open_system(" + systemHandlerName + ");"));
    this->engine->eval(convertUTF8StringToUTF16String("load_system('sflib');"));
    this->engine->eval(convertUTF8StringToUTF16String("add_block('sflib/Chart', ['" + modelName + "' '/Chart']);"));
    this->engine->eval(convertUTF8StringToUTF16String("rt = sfroot;"));
    this->engine->eval(convertUTF8StringToUTF16String("m = rt.find('-isa', 'Stateflow.Machine', 'name', '" + modelName + "');"));
    this->engine->eval(convertUTF8StringToUTF16String(parentChart + " = m.find('-isa', 'Stateflow.Chart');"));
    this->engine->eval(convertUTF8StringToUTF16String(parentChart + ".ChartUpdate = 'CONTINUOUS';"));

    /**
     * Build states and the corresponding ODEs for each state
     */
    for (const pdrh::mode &m : pdrh::modes){
        ostringstream slState, subSysHandler, positioningCommand;
        slState << translator::slStateBase << m.id;
        subSysHandler << translator::subSysHandlerBase << m.id;
        currentSubSystemHandler = subSysHandler.str();

        CLOG(INFO, "translator") << "*** Beginning translation of " << slState.str();

        positioningCommand << slState.str() << ".Position = [ " << xStatePosition << " " << yStatePosition << " 90 60];";
        yStatePosition += yIncrement;
        xStatePosition += xIncrement;
        this->engine->eval(convertUTF8StringToUTF16String(slState.str() + " = Stateflow.SimulinkBasedState(c);"));
        this->engine->eval(convertUTF8StringToUTF16String(slState.str() + ".Name = '" + slState.str() + "';"));
        this->engine->eval(convertUTF8StringToUTF16String(positioningCommand.str()));
        this->engine->eval(convertUTF8StringToUTF16String(subSysHandler.str() + " = " + slState.str() + ".getDialogProxy;"));

        for(pdrh::state s : pdrh::init){
            if (m.id == s.id){
                add_default_transition(s.id);
            }
        }
        this->generate_init_var_blocks(m);

        string scope_block_name = slState.str() + "_Scope";
        this->add_scope_block(this->currentSubSystemHandler, scope_block_name, m.odes.size());

        int scope_inport_counter = 1;
        for(auto it = m.odes.cbegin(); it != m.odes.cend(); it++){
            CLOG(INFO, "translator") << "Translating equation d[\"" << it->first << "\"]/dt" << endl;
            block_connection parent_ode_block = block_connection(it->first, 1);

            this->translate_ode_expression(it->second, parent_ode_block);
            this->connect_blocks(this->currentSubSystemHandler, parent_ode_block, block_connection(scope_block_name, scope_inport_counter++));

            CLOG(INFO, "translator") << "Completed translation of equation d[\"" << it->first << "\"]/dt" << endl;
        }

        // applicable to MATLAB R2018a+ only
        //TODO: detect matlab version and switch on/off the auto-arrange command
        try {
            string name = this->modelName + "/" + "Chart/" + slState.str();
            engine->eval(convertUTF8StringToUTF16String("Simulink.BlockDiagram.arrangeSystem('" + name + "');"));
        } catch (const matlab::engine::MATLABException& e) {
          CLOG(INFO, "translator") << "Attempted to arrange sub-system - Current MATLAB version doesn't support autoarranging.";
        }
    }

    /**
     * Connect all states and set all guards/reset conditions
     */
    CLOG(INFO, "translator") << "Adding state transitions ...";
    for (pdrh::mode m : pdrh::modes){
        CLOG_IF(global_config.verbose, INFO, "translator") << "Transitions for mode " << m.id;
        add_state_transition(m);
    }

    if (pdrh::time.first != NULL && pdrh::time.second != NULL){
        CLOG_IF(global_config.verbose, INFO, "translator") << "Setting simulation time to " << pdrh::time.second->value;
        this->engine->eval(convertUTF8StringToUTF16String("set_param(mdlName, 'StopTime', '" + pdrh::time.second->value +"');"));
    } else {
        CLOG(INFO, "translator") << "Simulation time not set, using default value of 10.";
    }

    this->engine->eval(convertUTF8StringToUTF16String("save_system(mdlName);"));
    CLOG(INFO, "translator" ) << "Completed translating model";
}

void translator::Translator::add_plant_transitions(const pdrh::mode &mode){
    stringstream slSourceState;
    slSourceState << slStateBase << mode.id;
    for (pdrh::mode::jump jump : mode.jumps){
        stringstream slDestState;
        slDestState << slStateBase << jump.next_id;
        CLOG_IF(global_config.verbose, INFO, "translator") << "Adding transition to mode " << jump.next_id << ":";
        /**
         * transition_new = Stateflow.Transition(c);
           transition_new.Source = ss1;
           transition_new.Destination = ss2;
         */
        this->engine->eval(convertUTF8StringToUTF16String("new_transition = Stateflow.Transition(" + parentChart + ");"));
        this->engine->eval(convertUTF8StringToUTF16String("new_transition.Source = " + slSourceState.str() + ";"));
        this->engine->eval(convertUTF8StringToUTF16String("new_transition.Destination = " + slDestState.str() + ";"));
        this->engine->eval(convertUTF8StringToUTF16String("new_transition.SourceOClock = 6;"));
        this->engine->eval(convertUTF8StringToUTF16String("new_transition.DestinationOClock = 0;"));

        stringstream reset_conditions;
        for (auto it = mode.odes.cbegin(); it != mode.odes.cend(); it++){
            reset_conditions << slDestState.str() << "." << it->first << " = " << it->first << "_in;";
        }

        stringstream transition_label;
        transition_label << "'[mode == " << jump.next_id << "]{"
                         << reset_conditions.str() << "}'";
        this->engine->eval(convertUTF8StringToUTF16String("new_transition.LabelString = " + transition_label.str() + ";"));

        CLOG_IF(global_config.verbose, INFO, "translator") << "Jump guard: " << translate_jump_guard(jump.guard, mode.id)<<endl;
        CLOG_IF(global_config.verbose, INFO, "translator") << "Jump resets: " << translate_reset_condition(jump, mode.id)<<endl;
    }
}

/**
 * Translates a node expression to a stateflow jump condition. Converts the expression tree to infix notation and
 * peforms substitution of logical operators.
 * @param guard
 * @param mode_id
 * @return Stateflow jump guard string
 */
string translator::Translator::controller_jump_guard(pdrh::node *guard, int mode_id)
{
    stringstream s, value;
    if (pdrh::var_map.count(guard->value)){
        value << guard->value << "_in";
    } else if (guard->value == "="){
        value << "==";
    } else if (guard->value == "and"){
        if (guard->operands.size() == 1){
            controller_jump_guard(guard->operands.front(), mode_id);
        } else {
            value << " & ";
        }
    } else if (guard->value == "or"){
        value << " | ";
    }
    else {
        value << guard->value;
    }
    // checking whether it is an operation node
    if(guard->operands.size() > 1)

    {
        s << "(";
        for(int i = 0; i < guard->operands.size() - 1; i++)
        {
            s << controller_jump_guard(guard->operands.at(i), mode_id);
            s << value.str();

        }
        s << controller_jump_guard(guard->operands.at(guard->operands.size() - 1), mode_id) << ")";
    }
    else if(guard->operands.size() == 1)
    {
        if(value.str() ==  "-")
        {
            s << "(" << value.str() << controller_jump_guard(guard->operands.front(), mode_id) << ")";
        }
        else
        {
            s << value.str() << "(" << controller_jump_guard(guard->operands.front(), mode_id) << ")";
        }
    }
    else
    {
        s << value.str();
    }
    return s.str();
}

string translator::Translator::controller_reset_condition(const pdrh::mode::jump &jump, const int source_mode_id){
    stringstream reset_condition;
    string targetState = slStateBase + to_string(jump.next_id);
    for(auto it = jump.reset.cbegin(); it != jump.reset.cend(); it++){
        reset_condition << it->first << "_out" << "="
                        << controller_reset_expression(it->second, source_mode_id) << ";";
    }
    reset_condition << "mode = " << jump.next_id << ";";

    return reset_condition.str();
}

/**
 * Translates the right-hand side of a reset condition in MATLAB syntax. Accepts a node pointer to an expression tree
 * which is then converted in infix notation.
 * @param reset_expr - pointer to the beginning of the syntax tree
 * @param mode_id - number label of the mode that's currently being translated
 * @return - string containing the translated expression
 */
string translator::Translator::controller_reset_expression(pdrh::node* reset_expr, int mode_id){
    stringstream s, value;
    if (pdrh::var_exists(reset_expr->value)){
        value << reset_expr->value << "_in";
    }
    else {
        value << reset_expr->value;
    }
    // checking if an operation is contained in the reset expression
    if(reset_expr->operands.size() > 1)

    {
        s << "(";
        for(int i = 0; i < reset_expr->operands.size() - 1; i++)
        {
            s << controller_reset_expression(reset_expr->operands.at(i), mode_id);
            s << value.str();

        }
        s << controller_reset_expression(reset_expr->operands.at(reset_expr->operands.size() - 1), mode_id) << ")";
    }
    else if(reset_expr->operands.size() == 1)
    {
        if(value.str() ==  "-")
        {
            s << "(" << value.str() << controller_reset_expression(reset_expr->operands.front(), mode_id) << ")";
        }
        else
        {
            s << value.str() << "(" << controller_reset_expression(reset_expr->operands.front(), mode_id) << ")";
        }
    }
    else
    {
        s << value.str();
    }
    return s.str();
};

void translator::Translator::add_controller_transitions(const pdrh::mode &mode){
    stringstream slSourceState;
    slSourceState << slStateBase << mode.id;
    for (pdrh::mode::jump jump : mode.jumps){
        stringstream slDestState;
        slDestState << slStateBase << jump.next_id;
        CLOG_IF(global_config.verbose, INFO, "translator") << "Adding transition to mode " << jump.next_id << ":";
        /**
         * transition_new = Stateflow.Transition(c);
           transition_new.Source = ss1;
           transition_new.Destination = ss2;
         */
        this->engine->eval(convertUTF8StringToUTF16String("new_transition = Stateflow.Transition(" + parentChart + ");"));
        this->engine->eval(convertUTF8StringToUTF16String("new_transition.Source = " + slSourceState.str() + ";"));
        this->engine->eval(convertUTF8StringToUTF16String("new_transition.Destination = " + slDestState.str() + ";"));
        this->engine->eval(convertUTF8StringToUTF16String("new_transition.SourceOClock = 6;"));
        this->engine->eval(convertUTF8StringToUTF16String("new_transition.DestinationOClock = 0;"));

        stringstream transition_label;
        transition_label << "'[" << controller_jump_guard(jump.guard, mode.id)
                         << "]{" << controller_reset_condition(jump, mode.id) << "}'";
        this->engine->eval(convertUTF8StringToUTF16String("new_transition.LabelString = " + transition_label.str() + ";"));

        CLOG_IF(global_config.verbose, INFO, "translator") << "Jump guard: " << controller_jump_guard(jump.guard, mode.id)<<endl;
        CLOG_IF(global_config.verbose, INFO, "translator") << "Jump resets: " << controller_reset_condition(jump, mode.id)<<endl;
    }
}

void translator::Translator::add_chart_data(string id, string scope){
        engine->eval(convertUTF8StringToUTF16String("d = Stateflow.Data(" + parentChart + ");"));
        engine->eval(convertUTF8StringToUTF16String("d.Scope = '" + scope + "';"));
        engine->eval(convertUTF8StringToUTF16String("d.Name = '" + id + "';"));
}

void translator::Translator::translate_model_decomposed(){
    int xStatePosition = 40;
    int yStatePosition = 120;
    const int yIncrement = 140;
    const int xIncrement = 100;

    string plant_ref_name = "Plant";
    string controller_ref_name = "Controller";

    this->modelName = modelName + "_decomposed";

    /**
     * Setup the system environment
     */
    this->engine->eval(convertUTF8StringToUTF16String("mdlName = '" + modelName + "'"));
    this->engine->eval(convertUTF8StringToUTF16String(systemHandlerName + " = new_system('" + modelName + "');"));
    this->engine->eval(convertUTF8StringToUTF16String("open_system(" + systemHandlerName + ");"));
    this->engine->eval(convertUTF8StringToUTF16String("load_system('sflib');"));
    this->engine->eval(convertUTF8StringToUTF16String("add_block('sflib/Chart', ['" + modelName + "' '/" + plant_ref_name + "']);"));
//    this->engine->eval(convertUTF8StringToUTF16String(plant_ref_name + ".Name = Plant;"));
//    this->engine->eval(convertUTF8StringToUTF16String(controller_ref_name + " = add_block('sflib/Chart', ['" + modelName + "' '/Chart']);"));
//    this->engine->eval(convertUTF8StringToUTF16String(controller_ref_name + ".Name = Controller;"));
    this->engine->eval(convertUTF8StringToUTF16String("rt = sfroot;"));
    this->engine->eval(convertUTF8StringToUTF16String("m = rt.find('-isa', 'Stateflow.Machine', 'name', '" + modelName + "');"));
    this->engine->eval(convertUTF8StringToUTF16String(parentChart + " = m.find('-isa', 'Stateflow.Chart');"));
    this->engine->eval(convertUTF8StringToUTF16String(parentChart + ".ChartUpdate = 'CONTINUOUS';"));

    /**
     * Add output ports to plant chart
     */
    for (auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++){
//        engine->eval(convertUTF8StringToUTF16String("d = Stateflow.Data(" + parentChart + ");"));
//        engine->eval(convertUTF8StringToUTF16String("d.Scope = 'Output';"));
//        engine->eval(convertUTF8StringToUTF16String("d.Name = '" + it->first + "_out';"));
        add_chart_data(it->first + "_out", "Output");
    };

    /**
     * Build states and the corresponding ODEs for each Plant state
     */
    for (const pdrh::mode &m : pdrh::modes) {
        ostringstream slState, subSysHandler, positioningCommand;
        slState << translator::slStateBase << m.id;
        subSysHandler << translator::subSysHandlerBase << m.id;
        currentSubSystemHandler = subSysHandler.str();

        CLOG(INFO, "translator") << "*** Beginning translation of " << slState.str();

        positioningCommand << slState.str() << ".Position = [ " << xStatePosition << " " << yStatePosition
                           << " 90 60];";
        yStatePosition += yIncrement;
        xStatePosition += xIncrement;
        this->engine->eval(convertUTF8StringToUTF16String(slState.str() + " = Stateflow.SimulinkBasedState(" + parentChart + ");"));
        this->engine->eval(convertUTF8StringToUTF16String(slState.str() + ".Name = '" + slState.str() + "';"));
        this->engine->eval(convertUTF8StringToUTF16String(positioningCommand.str()));
        this->engine->eval(
                convertUTF8StringToUTF16String(subSysHandler.str() + " = " + slState.str() + ".getDialogProxy;"));

        /**
         * Add default transitions
         */
        for (pdrh::state s : pdrh::init) {
            if (m.id == s.id) {
                add_default_transition(s.id);
            }
        }
        this->generate_init_var_blocks(m);

        /**
         * Scope blocks for simulink states
         */
        string scope_block_name = slState.str() + "_Scope";
        this->add_scope_block(this->currentSubSystemHandler, scope_block_name, m.odes.size());

        int scope_inport_counter = 1;
        for (const auto &ode : m.odes) {
            CLOG(INFO, "translator") << "Translating equation d[\"" << ode.first << "\"]/dt" << endl;

            block_connection parent_ode_block = block_connection(ode.first, 1);

            string outport_name = ode.first + "_out";
//            addBlock(this->currentSubSystemHandler, "simulink/Sinks/Out1", outport_name);

            this->translate_ode_expression(ode.second, parent_ode_block);
            this->connect_blocks(this->currentSubSystemHandler, parent_ode_block,
                                 block_connection(scope_block_name, scope_inport_counter++));
            this->connect_blocks(this->currentSubSystemHandler, parent_ode_block, block_connection(outport_name, 1));

            CLOG(INFO, "translator") << "Completed translation of equation d[\"" << ode.first << "\"]/dt" << endl;
        }
    }

    /**
     * Build plant transitions
     */

    for(const pdrh::mode &m: pdrh::modes){
        add_plant_transitions(m);
    }

    /**
     * Add input ports to plant chart
     */
    for (auto it = pdrh::var_map.cbegin(); it != pdrh::var_map.cend(); it++){
        add_chart_data(it->first + "_in", "Input");
    }

    /**
     * Add mode input (not included in the var_map)
     */
    add_chart_data("mode", "Input");


    /**
     * Add the controller chart
     */
    this->engine->eval(convertUTF8StringToUTF16String("add_block('sflib/Chart', ['" + modelName + "' '/" + controller_ref_name + "']);"));
    this->engine->eval(convertUTF8StringToUTF16String(parentChart + " = m.find('-isa', 'Stateflow.Chart', "
                                                                    "'-and', 'Name', '" + controller_ref_name + "');"));

    /**
     * Add controller states
     */
    for (const pdrh::mode &m : pdrh::modes) {
        ostringstream slState, subSysHandler, positioningCommand;
        slState << translator::slStateBase << m.id;
        subSysHandler << translator::subSysHandlerBase << m.id;
        currentSubSystemHandler = subSysHandler.str();

        CLOG(INFO, "translator") << "*** Beginning translation of " << slState.str();

        positioningCommand << slState.str() << ".Position = [ " << xStatePosition << " " << yStatePosition
                           << " 90 60];";
        yStatePosition += yIncrement;
        xStatePosition += xIncrement;
        this->engine->eval(convertUTF8StringToUTF16String(slState.str() + " = Stateflow.State(" + parentChart + ");"));
        this->engine->eval(convertUTF8StringToUTF16String(slState.str() + ".Name = '" + slState.str() + "';"));
        this->engine->eval(convertUTF8StringToUTF16String(positioningCommand.str()));
        this->engine->eval(
                convertUTF8StringToUTF16String(subSysHandler.str() + " = " + slState.str() + ".getDialogProxy;"));

        /**
         * Add default transitions
         */
        for (pdrh::state &s : pdrh::init) {
            if (m.id == s.id) {
                add_default_transition(s.id);
            }
        }
    }

    /**
     * Add controller transitions
     */
    for (pdrh::mode &m : pdrh::modes){
        add_controller_transitions(m);
    }

    /**
     * Add controller chart input/outputs
     */
    for(auto var: pdrh::var_map){
        add_chart_data(var.first + "_in", "Input");
        add_chart_data(var.first + "_out", "Output");
    }
    add_chart_data("mode", "Output");

    /**
     * Connect plant to controller and vice-versa
     */
//    engine->eval(convertUTF8StringToUTF16String(currentSubSystemHandler + " = rt.find('-isa','Simulink.BlockDiagram');"));
    currentSubSystemHandler = "m";
    ostringstream add_line_command;
    int port_counter = 1;
    for (const auto &var : pdrh::var_map){
        string mem_block_name = var.first + "_mem";
        cout<<"adding mem block: " << mem_block_name << ", current port: " << port_counter << endl;
        this->engine->eval(convertUTF8StringToUTF16String("add_block('simulink/Discrete/Memory', "
                                                          "['" + modelName + "' '/" + mem_block_name + "']);"));
        cout<< "connecting plant to mem..." << endl;
        add_line_command << "add_line('" + modelName + "', '"
                         << plant_ref_name << "/" << port_counter << "', '"
                         << mem_block_name << "/" << "1"
                         << "', 'autorouting', 'smart');";

        cout<< "connecting mem to controller ..." << endl;
        add_line_command << "add_line('" + modelName + "', '"
                         << mem_block_name << "/" << "1" << "', '"
                         << controller_ref_name << "/" << port_counter
                         << "', 'autorouting', 'smart');";

        cout<< "connecting controller to plant ..." << endl;
        add_line_command << "add_line('" + modelName + "', '"
                         << controller_ref_name << "/" << port_counter << "', '"
                         << plant_ref_name << "/" << port_counter
                         << "', 'autorouting', 'smart');";

        cout<< add_line_command.str() << endl;
//        connect_blocks(currentSubSystemHandler, plant_ref_name, var.first + "_out", mem_block_name, "1");
//        connect_blocks(currentSubSystemHandler, mem_block_name, "1", controller_ref_name, var.first + "_in");
//        connect_blocks(currentSubSystemHandler, controller_ref_name, var.first + "_out", plant_ref_name, var.first + "_in");
        engine->eval(convertUTF8StringToUTF16String(add_line_command.str()));
        add_line_command.str("");
        port_counter++;
    }
    // connect the mode output from the controller
    add_line_command << "add_line('" + modelName + "', '"
                     << controller_ref_name << "/" << port_counter << "', '"
                     << plant_ref_name << "/" << port_counter
                     << "', 'autorouting', 'smart');";
    engine->eval(convertUTF8StringToUTF16String(add_line_command.str()));

    this->engine->eval(convertUTF8StringToUTF16String("save_system(mdlName);"));
    CLOG(INFO, "translator" ) << "Completed translating model";
}

/**
 * Translates the right-hand side of a reset condition in MATLAB syntax. Accepts a node pointer to an expression tree
 * which is then converted in infix notation.
 * @param reset_expr - pointer to the beginning of the syntax tree
 * @param mode_id - number label of the mode that's currently being translated
 * @return - string containing the translated expression
 */
string translator::Translator::translate_reset_expression(pdrh::node* reset_expr, int mode_id){
    stringstream s, value;
    if (pdrh::var_exists(reset_expr->value)){
        value << slStateBase << mode_id << "." << reset_expr->value;
    }
    else {
        value << reset_expr->value;
    }
    // checking if an operation is contained in the reset expression
    if(reset_expr->operands.size() > 1)

    {
        s << "(";
        for(int i = 0; i < reset_expr->operands.size() - 1; i++)
        {
            s << translate_reset_expression(reset_expr->operands.at(i), mode_id);
            s << value.str();

        }
        s << translate_reset_expression(reset_expr->operands.at(reset_expr->operands.size() - 1), mode_id) << ")";
    }
    else if(reset_expr->operands.size() == 1)
    {
        if(value.str() ==  "-")
        {
            s << "(" << value.str() << translate_reset_expression(reset_expr->operands.front(), mode_id) << ")";
        }
        else
        {
            s << value.str() << "(" << translate_reset_expression(reset_expr->operands.front(), mode_id) << ")";
        }
    }
    else
    {
        s << value.str();
    }
    return s.str();
};

/**
 * Builds the entire reset condition by joining together left-hand side identifiers to their expressions.
 * @param jump - the transition in question
 * @param source_mode_id - the number label of the source transition
 * @return - a complete reset condition string
 */
string translator::Translator::translate_reset_condition(pdrh::mode::jump &jump, int source_mode_id) {
    stringstream reset_condition;
    string targetState = slStateBase + to_string(jump.next_id);
    for(auto it = jump.reset.cbegin(); it != jump.reset.cend(); it++){
        reset_condition << targetState << "." << it->first << "="
                        << translate_reset_expression(it->second, source_mode_id) << ";";
    }
        return reset_condition.str();
}

/**
 * Adds a default (initial) transition to the designated mode.
 * @param start_node - number labe of a mode
 */
void translator::Translator::add_default_transition(int start_node) {
    stringstream defaultModeName;
    defaultModeName << slStateBase << start_node;
    this->engine->eval(convertUTF8StringToUTF16String("new_transition = Stateflow.Transition(" + parentChart + ");"));
    this->engine->eval(convertUTF8StringToUTF16String("new_transition.Destination = " + defaultModeName.str() + ";"));
    this->engine->eval(convertUTF8StringToUTF16String("new_transition.DestinationOClock = 0;"));
}


void addBlock(const unique_ptr<MATLABEngine>& engine, string systemHandler, string subSysHandler, string srcPath, string blkName) {
    string commandString = systemHandler +  " = add_block('" + srcPath + "', fullfile(" + subSysHandler +".Path, " +
                           subSysHandler + ".Name, '" + blkName + "'));";
    engine->eval(convertUTF8StringToUTF16String(commandString));
}

void addBlock(const unique_ptr<MATLABEngine>& engine, string systemHandler, string subSysHandler,
              string srcPath, string blkName, translator::block_connection previous_block) {
    ostringstream add_block_command;
    add_block_command << systemHandler << " = add_block('" << srcPath << "', fullfile(" << subSysHandler
                      << ".Path, " << subSysHandler << ".Name, '" << blkName + "'));";
    engine->eval(convertUTF8StringToUTF16String(add_block_command.str()));
//    string add_line_command = "add_line(fullfile(" + subSysHandler +".Path, " +
//    subSysHandler + ".Name), '" + blkName + "/1', '" + previous_block.block_name + "/'";
    ostringstream add_line_command;
    add_line_command << "add_line(fullfile(" << subSysHandler << ".Path, " << subSysHandler << ".Name), '"
                     << blkName << "/1', '" << previous_block.block_name << "/" << previous_block.port_id
                     << "', 'autorouting', 'on');";
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

    return 0;
}

/**
 * Resolves initial value for the given variable name string.
 * Performs look-up in the initial conditions for a variable and maps either a uniform distribution
 * or a concrete initial value.
 * @param variable_name - name of variable
 * @return - string containing the initial value or random number function
 */
string translator::get_initial_value(string variable_name){
    //TODO: add the other random distributions
    bool located = false;
    string lower_bound, upper_bound;
    for(pdrh::state s : pdrh::init){
        for(unsigned int i = 0; i < s.prop->operands.size(); i++){
            pdrh::node* node = s.prop->operands.at(i);
            if (node->operands.at(0)->value == variable_name){
                located = true;
                if (node->value == "="){
                    return translator::resolve_variable_init_expr(node->operands.at(1));
                } else {
                    if (node->value == ">="){
                        lower_bound = translator::resolve_variable_init_expr(node->operands.at(1));
                    } else if (node->value == "<="){
                        upper_bound = translator::resolve_variable_init_expr(node->operands.at(1));
                    }
                }
            }
        }
    }

    if (located) {
        return lower_bound + "+(" + upper_bound + "-" + lower_bound + ").*rand(1,1)";
    // If we didn't find the variable above...
    } else {
        if (pdrh::rv_map.find(variable_name) != pdrh::rv_map.end()){
            pdrh::node rv = pdrh::node(variable_name);
            return resolve_variable_init_expr(&rv);
        }
        CLOG(WARNING, "translator" ) << "Initial condition for " << variable_name
                                     << " not defined - using lower bound of its domain as initial condition.";
        // Look in the var-map for its interval and use the lower bound as default value
        auto iter = pdrh::var_map.find(variable_name);
        if (iter != pdrh::var_map.end() && iter->second.first != nullptr){
            string init_value = resolve_variable_init_expr(iter->second.first);
            CLOG(INFO, "translator") << "Lower bound: " << init_value << endl;
            return init_value;
        }
        // as a further fail-safe, return 0
        else {
            CLOG(WARNING, "translator" ) << "Variable " << variable_name << "not found in variable map, setting initial value to 0";
            return "0";
        }
    }
}

void translator::translate(){
    translator::Translator* translator1 = new Translator();
//    translator1->translate_model();
    translator1->translate_model_decomposed();
    delete translator1;
}

string translate_distributions(pdrh::node *node){
    stringstream value;
    auto normal_iter = pdrh::distribution::normal.find(node->value);
    if (normal_iter != pdrh::distribution::normal.end()){
        value << "normrnd(" <<  translator::resolve_variable_init_expr(normal_iter->second.first)
              << ", " << translator::resolve_variable_init_expr(normal_iter->second.second) << ")";
        return value.str();
    }

    auto exp_iter = pdrh::distribution::exp.find(node->value);
    if (exp_iter != pdrh::distribution::exp.end()){
        value << "exprnd(" <<  translator::resolve_variable_init_expr(exp_iter->second) << ")";
        return value.str();
    }

    auto gamma_iter = pdrh::distribution::gamma.find(node->value);
    if (gamma_iter != pdrh::distribution::gamma.end()){
        value << "gammarnd(" <<  translator::resolve_variable_init_expr(gamma_iter->second.first)
              << ", " << translator::resolve_variable_init_expr(gamma_iter->second.second) << ")";
        return value.str();
    }

    auto uniform_iter = pdrh::distribution::uniform.find(node->value);
    if (uniform_iter != pdrh::distribution::uniform.end()){
        value << "unifrnd(" <<  translator::resolve_variable_init_expr(uniform_iter->second.first)
              << ", " << translator::resolve_variable_init_expr(uniform_iter->second.second) << ")";
        return value.str();
    }
    return "";
}

/**
 * Translates a variables initial condition right-hand side expression to infix notation as used in MATLAB.
 * @param node - root of the expression tree
 * @return - string containing the infix representation
 */
string translator::resolve_variable_init_expr(pdrh::node *node) {
    stringstream s, value;
    if (pdrh::var_exists(node->value)){
        if (pdrh::rv_map.find(node->value) != pdrh::rv_map.end()){
            value << translate_distributions(node);
        } else {
            value << translator::get_initial_value(node->value);
        }
    }
    else {
        value << node->value;
    }
    // checking whether it is an operation reset_expr
    if(node->operands.size() > 1)

    {
        s << "(";
        for(int i = 0; i < node->operands.size() - 1; i++)
        {
            s << resolve_variable_init_expr(node->operands.at(i));
            s << value.str();

        }
        s << resolve_variable_init_expr(node->operands.at(node->operands.size() - 1)) << ")";
    }
    else if(node->operands.size() == 1)
    {
        if(value.str() ==  "-")
        {
            s << "(" << value.str() << resolve_variable_init_expr(node->operands.front()) << ")";
        }
        else
        {
            s << value.str() << "(" << resolve_variable_init_expr(node->operands.front()) << ")";
        }
    }
    else
    {
        s << value.str();
    }
    return s.str();
};

