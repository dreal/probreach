//
// Created by fedor on 26/02/16.
//

#include <fstream>
#include <stdexcept>
#include <sstream>
#include "dreal_wrapper.h"
#include <algorithm>

using namespace std;

const vector<string> SAT_ANSWERS = {"sat", "delta-sat"};
const vector<string> UNSAT_ANSWERS = {"unsat"};

// parsing output given the name of the file
int parse_output(string output)
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
    string last_line, line;
    while(getline(output_file, line))
    {
        last_line = line;
    }
    output_file.close();
    // analyzing the last line of the output
    string res;
    unsigned long pos = last_line.find_first_of(" ");
    if(pos != string::npos)
    {
        res = last_line.substr(0, pos);
    }
    else
    {
        res = last_line;
    }
    // checking if the output line is a sat answer
    if(find(SAT_ANSWERS.begin(), SAT_ANSWERS.end(), res) != SAT_ANSWERS.end())
    {
        return 0;
    }
    else if(find(UNSAT_ANSWERS.begin(), UNSAT_ANSWERS.end(), res) != UNSAT_ANSWERS.end())
    // checking if the output line is an unsat answer
    {
        return 1;
    }
    else
    // unrecognized answer
    {
        stringstream s;
        s << "Unrecognized solver output: " << res;
        throw runtime_error(s.str());
    }
}

int dreal::execute(std::string bin, std::string input, std::string args)
{
    stringstream s;
    s << bin << " " << args << " " << input << " > " << input << ".output";
    //s << bin << " " << args << " --visualize " << input << " > " << input << ".output && cp " << input << ".json " << input << "." << time(0) << ".json";
    int res = system(s.str().c_str());
    if (res != 0)
    {
        stringstream e;
        e << "Unexpected problem running: " << s.str();
        throw runtime_error(e.str());
    }
    return parse_output(input + ".output");
}

