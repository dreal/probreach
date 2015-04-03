#include<string.h>
#include<sstream>
#include<iostream>
#include<fstream>
#include<algorithm>
#include<limits>
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include "CSVParser.h"

using namespace capd;
using namespace std;

std::map<string, vector<double> > CSVParser::parse(string filename)
{
    ifstream file;
    file.open(filename.c_str());

    std::map<string, vector<double> > result;

    if(file.is_open())
    {
        string line;
        getline(file, line);
        line.erase(remove(line.begin(), line.end(), ' '), line.end());

        vector<string> cols;
        string delimiter = ",";
        size_t pos = 0;
        while ((pos = line.find(delimiter)) != std::string::npos)
        {
            cols.push_back(line.substr(0, pos));
            line.erase(0, pos + delimiter.length());
        }
        cols.push_back(line.substr(0, line.length() - 1));

        while (getline(file, line))
        {
            //cout << line << endl;
            for(int i = 0; i < cols.size() - 1; i++)
            {
                pos = line.find(delimiter);
                istringstream is(line.substr(0, pos));
                double value = numeric_limits<double>::quiet_NaN();
                if(!is.str().empty())
                {
                    is >> value;
                }
                result[cols.at(i)].push_back(value);
                line.erase(0, pos + delimiter.length());
            }

            istringstream is(line.substr(0, line.length() - 1));
            double value = numeric_limits<double>::quiet_NaN();
            if(!is.str().empty())
            {
                is >> value;
            }
            result[cols.at(cols.size() - 1)].push_back(value);
        }
    }
    else
    {
        cerr << "Could not open file " << filename << endl;
    }

    return result;
}

std::map<string, vector<DInterval> > CSVParser::parse(string filename, double noise)
{
    std::map<string, vector<DInterval> > result;
    std::map<string, vector<double> > csv = parse(filename);
    for(auto it = csv.begin(); it != csv.end(); it++)
    {
        for(int i = 0; i < it->second.size(); i++)
        {
            DInterval interval;
            if(!std::isnan(it->second.at(i)))
            {
                if((strcmp(it->first.c_str(), "Time") == 0) ||
                        (strcmp(it->first.c_str(), "Mode") == 0) ||
                            (strcmp(it->first.c_str(), "Step") == 0))
                {
                    result[it->first].push_back(DInterval(it->second.at(i)));
                }
                else
                {
                    result[it->first].push_back(DInterval(it->second.at(i) - noise, it->second.at(i) + noise));
                }
            }
            else
            {
                result[it->first].push_back(DInterval(numeric_limits<double>::quiet_NaN(), numeric_limits<double>::quiet_NaN()));
            }
        }
    }
    return result;
}

void CSVParser::display(std::map<string, vector<double> > csv, string (delimiter))
{
    for(auto it = csv.begin(); it != csv.end(); it++)
    {
        cout << "|" << it->first << delimiter << flush;
    }
    cout << "|" << endl;

    int row_number = csv.begin()->second.size();
    for(int i = 0; i < row_number; i++)
    {
        for(auto it = csv.begin(); it != csv.end(); it++)
        {
            cout << "|" << csv[it->first].at(i) << delimiter << flush;
        }
        cout << "|" << endl;
    }
}

void CSVParser::display(std::map<string, vector<DInterval>> csv, string (delimiter))
{
    for(auto it = csv.begin(); it != csv.end(); it++)
    {
        cout << "|" << it->first << delimiter << flush;
    }
    cout << "|" << endl;

    int row_number = csv.begin()->second.size();
    for(int i = 0; i < row_number; i++)
    {
        for(auto it = csv.begin(); it != csv.end(); it++)
        {
            cout << "|" << csv[it->first].at(i) << delimiter << flush;
        }
        cout << "|" << endl;
    }
}


