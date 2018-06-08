//
// Created by fedor on 26/02/16.
//

#include <fstream>
#include <stdexcept>
#include <sstream>
#include "dreal_wrapper.h"
#include <algorithm>
#include "box.h"

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


pair<string, int> get_depth_index(string line)
{
    // removing "t" from the end of the line
    line = line.substr(0, line.size() - 2);
    size_t last_pos = line.find_last_of("_");
    int index;
    istringstream ss(line.substr(last_pos + 1, line.size() - 1));
    ss >> index;
    return make_pair(line.substr(0, last_pos), index);
}


box dreal::parse_model(string filename)
{
    fstream model_file;
    model_file.open(filename.c_str());
    if(!model_file.is_open())
    {
        stringstream s;
        s << "Problem opening the file " << filename;
        throw runtime_error(s.str());
    }
    // getting the last line of the file
    string line;
    // skipping the first line
    getline(model_file, line);
    // concatenated string
    string cat_line = "";
    while(getline(model_file, line))
    {
        cat_line += line;
    }
    model_file.close();
    box entire_box(cat_line.append(";"));
    // getting the largest index of the variables
    map<string, capd::interval> entire_map = entire_box.get_map();
    int max_index = 0;
    for(auto it = entire_map.begin(); it != entire_map.end(); it++)
    {
        if(get_depth_index(it->first).second > max_index)
        {
            max_index = get_depth_index(it->first).second;
        }
    }
    // creating a map with "t" indexed variables and the largest index
    map<string, capd::interval> b_map;
    for(auto it = entire_map.begin(); it != entire_map.end(); it++)
    {
        pair<string, int> var = get_depth_index(it->first);
        if(var.second == max_index && it->first.back() == 't')
        {
            b_map.insert(make_pair(var.first, it->second));
        }
    }
    b_map["time"] = entire_map["time"];
    return box(b_map);
}
















