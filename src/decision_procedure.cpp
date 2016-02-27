//
// Created by fedor on 26/02/16.
//

#include "decision_procedure.h"
#include "solver/dreal_wrapper.h"
#include "pdrh_config.h"

int decision_procedure::evaluate(std::vector<pdrh::mode *> path, std::vector<box> boxes)
{
    // getting raw filename here
    std::string filename = std::string(global_config.model_filename);
    size_t ext_index = filename.find_last_of('.');
    std::string raw_filename = filename.substr(0, ext_index);
    // creating a name for the smt2 file
    std::stringstream f_stream;
    f_stream << raw_filename << "_" << path.size() - 1 << "_0.smt2";
    std::string smt_filename = f_stream.str();
    // writing to the file
    std::ofstream smt_file;
    smt_file.open(smt_filename.c_str());
    smt_file << pdrh::reach_to_smt2(path, boxes);
    smt_file.close();
    // calling dreal here
    int first_res = dreal::execute(global_config.solver_bin, smt_filename, global_config.solver_opt);
    if(first_res == -1)
    {
        return decision_procedure::ERROR;
    }
    else if(first_res == 1)
    {
        if((std::remove(smt_filename.c_str()) == 0) &&
                (std::remove(std::string(smt_filename + ".output").c_str()) == 0))
        {
            return decision_procedure::UNSAT;
        }
        else
        {
            std::cout << "Problem occurred while removing one of auxiliary files" << std::endl;
            return decision_procedure::ERROR;
        }
    }
    else
    {
        // the complement formula
        f_stream.str("");
        f_stream << raw_filename << "_" << path.size() - 1 << "_0.c.smt2";
        std::string smt_c_filename = f_stream.str();
        // writing to the file
        std::ofstream smt_c_file;
        smt_c_file.open(smt_c_filename.c_str());
        smt_c_file << pdrh::reach_c_to_smt2(path, boxes);
        smt_c_file.close();
        // calling dreal here
        int second_res = dreal::execute(global_config.solver_bin, smt_c_filename, global_config.solver_opt);
        if(second_res == -1)
        {
            return decision_procedure::ERROR;
        }
        else if(second_res == 1)
        {
            if((std::remove(smt_c_filename.c_str()) == 0) &&
                (std::remove(std::string(smt_c_filename + ".output").c_str()) == 0) &&
                    (std::remove(smt_filename.c_str()) == 0) &&
                        (std::remove(std::string(smt_filename + ".output").c_str()) == 0))
            {
                return decision_procedure::SAT;
            }
            else
            {
                std::cout << "Problem occurred while removing one of auxiliary files" << std::endl;
                return decision_procedure::ERROR;
            }
        }
        else
        {
            if((std::remove(smt_c_filename.c_str()) == 0) &&
                (std::remove(std::string(smt_c_filename + ".output").c_str()) == 0) &&
                    (std::remove(smt_filename.c_str()) == 0) &&
                        (std::remove(std::string(smt_filename + ".output").c_str()) == 0))
            {
                return decision_procedure::UNDET;
            }
            else
            {
                std::cout << "Problem occurred while removing one of auxiliary files" << std::endl;
                return decision_procedure::ERROR;
            }
        }
    }
}