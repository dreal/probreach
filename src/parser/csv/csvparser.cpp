//
// Created by fedor on 04/03/16.
//

#include <fstream>
#include <string.h>
#include <easylogging++.h>
#include "csvparser.h"

std::map<std::string, std::vector<capd::interval>> csvparser::parse(std::string filename)
{
    std::ifstream file;
    std::map<std::string, std::vector<capd::interval> > result;
    std::map<std::string, std::vector<double> > noise_vector;
    file.open(filename.c_str());
    if(file.is_open())
    {
        std::string line;
        getline(file, line);

        //stripping the string
        line.erase(remove(line.begin(), line.end(), ' '), line.end());

        // fetching column names
        std::vector<std::string> cols, vars;
        std::string delimiter = ",";
        size_t pos = 0;
        while ((pos = line.find(delimiter)) != std::string::npos)
        {
            cols.push_back(line.substr(0, pos));
            line.erase(0, pos + delimiter.length());
        }
        cols.push_back(line.substr(0, line.length() - 1));

        // creating noise vector
        for(int i = 0; i < cols.size(); i++)
        {
            smatch matches;

            // default noise value
            double noise = 0.1;
            // var name
            string var_name = cols.at(i);
            // checking if noise value is specified
            if(regex_match(cols.at(i), matches, regex("(.*):(.*)")))
            {
                var_name = matches[1].str();
                istringstream is(matches[2]);
                is >> noise;
                if(noise <= 0)
                {
                    CLOG(ERROR, "series-parser") << "Noise value should be positive for " << var_name;
                    exit(EXIT_FAILURE);
                }
            }
            if((strcmp(var_name.c_str(), "Mode") == 0) ||
               (strcmp(var_name.c_str(), "Step") == 0) ||
               (strcmp(var_name.c_str(), "Time") == 0))
            {
                noise = 0;
            }
            noise_vector[var_name].push_back(noise);
            vars.push_back(var_name);
        }

        // fetching data
        while (getline(file, line))
        {
            for(int i = 0; i < vars.size() - 1; i++)
            {
                pos = line.find(delimiter);
                std::istringstream is(line.substr(0, pos));
                double value = numeric_limits<double>::quiet_NaN();
                if(!is.str().empty())
                {
                    is >> value;
                    //cout << value << endl;
                }
                capd::interval interval(value);
                if((strcmp(vars.at(i).c_str(), "Time") != 0) &&
                   (strcmp(vars.at(i).c_str(), "Mode") != 0) &&
                   (strcmp(vars.at(i).c_str(), "Step") != 0))
                {
                    interval = capd::interval(value - noise_vector[vars.at(i)].at(0), value + noise_vector[vars.at(i)].at(0));
                }
                result[vars.at(i)].push_back(interval);

                line.erase(0, pos + delimiter.length());
            }
            // last value in data
            std::istringstream is(line.substr(0, line.length() - 1));
            double value = numeric_limits<double>::quiet_NaN();
            if(!is.str().empty())
            {
                is >> value;
            }
            capd::interval interval(value);
            if((strcmp(vars.at(vars.size() - 1).c_str(), "Time") != 0) &&
               (strcmp(vars.at(vars.size() - 1).c_str(), "Mode") != 0) &&
               (strcmp(vars.at(vars.size() - 1).c_str(), "Step") != 0))
            {
                interval = capd::interval(value - noise_vector[vars.at(vars.size() - 1)].at(0), value + noise_vector[vars.at(vars.size() - 1)].at(0));
            }
            result[vars.at(vars.size() - 1)].push_back(interval);
        }
    }
    else
    {
        CLOG(ERROR, "series-parser") << "Could not open file " << filename;
        exit(EXIT_FAILURE);
    }
    return result;
}