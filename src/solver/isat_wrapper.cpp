//
// Created by fedor on 03/03/17.
//

#include <sstream>
#include <stdexcept>
#include <vector>
#include <fstream>
#include "isat_wrapper.h"

const string UNKNOWN_ANSWER = "unknown";
const string UNSAT_ANSWER = "unsatisfiable";
const string SAT_ANSWER = "Target state evaluates to:  true";

using namespace std;

solver::output parse_isat_output(string output)
{
    fstream output_file;
    output_file.open(output.c_str());
    if(!output_file.is_open())
    {
        stringstream s;
        s << "Problem opening the file " << output;
        throw runtime_error(s.str());
    }
    // getting the last line of the file
    string first_line;
    getline(output_file, first_line);
    output_file.close();
    remove(output.c_str());
    if(first_line.find(UNKNOWN_ANSWER) != string::npos)
    {
        return solver::SAT;
    }
    else if(first_line.find(UNSAT_ANSWER) != string::npos)
    {
        return solver::UNSAT;
    }
    else
    {
        stringstream s;
        s << "Unrecognized solver output: " << first_line;
        throw runtime_error(s.str());
    }
}

solver::output isat::evaluate(string path, string input, string args)
{
    stringstream s;
    s << path << " --i " << input << " " << args << " 2> /dev/null | sed '1,/RESULT:/d' > " << input << ".output";
    //s << path << " --i " << input << " " << args;
    int res = system(s.str().c_str());
    if (res != 0)
    {
        stringstream e;
        e << "Unexpected problem running: " << s.str();
        throw runtime_error(e.str());
    }
    return parse_isat_output(input + ".output");
}