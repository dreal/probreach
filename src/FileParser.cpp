// FileParser class implements a parser for the
// files in PDRH format
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#include<string>
#include<sstream>
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<regex>
#include "BoxFactory.h"
#include "Box.h"
#include "PartialSum.h"
#include "FileParser.h"
#include "RV.h"
#include "nRV.h"

using namespace std;
using namespace capd;

// Constructor of the class
//
// @param full path to the settings file
FileParser::FileParser(string filename)
{
	parse_settings(filename);
	this->model = this->settings["model"];
	this->model_c = this->settings["model_c"];
	if ((this->model != "") && (this->model_c != ""))
	{
		parse_pdrh(this->model);
		parse_pdrh_c(this->model_c);
		modify_init();
		modify_flows();
	}
}

// The methods performs all the necessary changes to
// the "init" section of PDRH file
void FileParser::modify_init()
{
	const regex init_line_regex("(.*@[0-9])\\s*(\\(.*\\));.*");
	const regex line("\\s*(.*)\\s*$");
	
	for(int i = 0; i < temp.size(); i++)
	{
		if(regex_match(temp.at(i), regex(".*(init:).*")))
		{
			smatch matches;
			int start_init = i + 1;
			stringstream init_stream;
			int j = i + 1;
			while(!regex_match(temp.at(j), regex(".*(goal:).*")))
			{
				if(regex_match(temp.at(j), matches, line))
				{
					init_stream << matches[1].str();
				}
				j++;
			}
			int end_init = j;
			if(regex_match(init_stream.str(), matches, init_line_regex))
			{
				string matches1 = matches[1].str();
				string matches2 = matches[2].str();
				string init = matches1 + " (and " + matches2 + " ";
				for(int j = 0; j < rv.size(); j++)
				{
					string var = rv.at(j)->get_var();
					init += " (" + var + " >= " + var + "_a)" + " (" + var + " <= " + var + "_b)";
				}
				init += ");";
				temp.erase(temp.begin() + start_init, temp.begin() + end_init);
				temp.insert(temp.begin() + start_init, init);
				break;
			}
		}
	}
	
	for(int i = 0; i < temp_inv.size(); i++)
	{
		if(regex_match(temp_inv.at(i), regex(".*(init:).*")))
		{
			smatch matches;
			int start_init = i + 1;
			stringstream init_stream;
			int j = i + 1;
			while(!regex_match(temp_inv.at(j), regex(".*(goal:).*")))
			{
				if(regex_match(temp_inv.at(j), matches, line))
				{
					init_stream << matches[1].str();
				}
				j++;
			}
			int end_init = j;
			if(regex_match(init_stream.str(), matches, init_line_regex))
			{
				string matches1 = matches[1].str();
				string matches2 = matches[2].str();
				string init = matches1 + " (and " + matches2 + " ";
				for(int j = 0; j < rv.size(); j++)
				{
					string var = rv.at(j)->get_var();
					init += " (" + var + " >= " + var + "_a)" + " (" + var + " <= " + var + "_b)";
				}
				init += ");";
				temp_inv.erase(temp_inv.begin() + start_init, temp_inv.begin() + end_init);
				temp_inv.insert(temp_inv.begin() + start_init, init);
				break;
			}
		}
	}
}

// The methods performs all the necessary changes to
// the "flow" sections of PDRH file
void FileParser::modify_flows()
{
	const regex ode_regex(".*d/dt\\[([A-Za-z][A-Za-z0-9]*)\\]+.*");
	vector<string> flow_map;
	smatch matches;
	int n = temp.size();
	int i = 0;
	while(i < n)
	{
		if(regex_match(temp.at(i), regex(".*(jump).*(:).*")))
		{
			for(int j = 0; j < rv.size(); j++)
			{
				if (find(flow_map.begin(), flow_map.end(), rv.at(j)->get_var()) == flow_map.end())
				{
					string ode = "\td/dt[" + rv.at(j)->get_var() + "]=0.0;";
					temp.insert(temp.begin() + i, ode);
					i++;
					n++;
				}
			}
			flow_map.clear();
		}
		if(regex_match(temp.at(i), matches, ode_regex))
		{
			if (find(flow_map.begin(), flow_map.end(), matches[1].str()) == flow_map.end())
			{
				flow_map.push_back(matches[1].str());
			}
		}
		i++;
	}

	n = temp_inv.size();
	i = 0;
	while(i < n)
	{
		if(regex_match(temp_inv.at(i), regex(".*(jump).*(:).*")))
		{
			for(int j = 0; j < rv.size(); j++)
			{
				if (find(flow_map.begin(), flow_map.end(), rv.at(j)->get_var()) == flow_map.end())
				{
					string ode = "\td/dt[" + rv.at(j)->get_var() + "]=0.0;";
					temp_inv.insert(temp_inv.begin() + i, ode);
					i++;
					n++;
				}
			}
			flow_map.clear();
		}
		if(regex_match(temp_inv.at(i), matches, ode_regex))
		{
			if (find(flow_map.begin(), flow_map.end(), matches[1].str()) == flow_map.end())
			{
				flow_map.push_back(matches[1].str());
			}
		}
		i++;
	}
}

/*
void FileParser::modify_jumps()
{
	const regex jump_regex("(.*==>.*)(\\(\\));");
	smatch matches;
	for(int i = 0; i < temp.size(); i++)
	{
		if(regex_match(temp.at(i), matches, jump_regex))
		{
			string jump = matches[1].str() + " (and " + matches[2].str();
			for(int j = 0; j < rv.size(); j++)
			{
				string var = rv.at(j)->get_var();
				const regex jump_rv_regex(".*" + var + "'.*");

				if(!regex_match(temp.at(i), jump_rv_regex))
				{
					jump += "(" + var + "'=" + var + ")";
				}
			}
			jump += ");";
			temp.at(i) = jump;
		}
	}
}
*/

// The methods parses the settings provided as
// an input for the application
//
// @param full path to the settings file
void FileParser::parse_settings(string filename)
{
	ifstream settings_file;
	settings_file.open(filename.c_str());
	const regex precision_regex("\\s*precision\\s*:\\s*");
	const regex model_regex("\\s*model\\s*:\\s*");
	const regex depth_regex("\\s*depth\\s*:\\s*");

	if (settings_file.is_open())
	{
		while (!settings_file.eof())
		{
			string line;
			getline(settings_file, line);
			if (regex_match(line, precision_regex))
			{
				getline(settings_file, line);
				smatch matches;
				const regex positive_float_regex("\\s*([0-9]+.[0-9]*)\\s*");
				if(regex_match(line, matches, positive_float_regex))
				{
					settings["precision"] = matches[1];
				}
			}
			if (regex_match(line, model_regex))
			{
				getline(settings_file, line);
				settings["model"] = line;
				getline(settings_file, line);
				settings["model_c"] = line;
			}
			if (regex_match(line, depth_regex))
			{
				getline(settings_file, line);
				smatch matches;
				regex positive_int_regex("\\s*([0-9]+)\\s*");
				if (regex_match(line, matches, positive_int_regex)) 
				{
					settings["depth"] = matches[1];
				}
			}
		}
		settings_file.close();
	}
}

// The methods parses PDRH file
//
// @param full path to the PDRH file
void FileParser::parse_pdrh(string filename)
{
	const regex normal_regex("(\\s)*(N)(\\s)*(\\()([-+]?[0-9]*.?[0-9]+)(\\s)*(,)(\\s)*([-+]?[0-9]*.?[0-9]+)(\\s)*(\\))(\\s)*([a-zA-Z][a-zA-Z0-9_]*)(;)(\\s)*");

	ifstream file;
	file.open(filename.c_str());
	smatch matches;
	
	if(file.is_open())
	{
		string line;
		while (getline(file, line))
		{
			if (regex_match(line, matches, normal_regex)) 
			{
				string param1 = string() + matches[5].str();
				double mean = atof(param1.c_str());
				string param2 = string() + matches[9].str();
				double deviation = atof(param2.c_str());
				string var = string() + matches[13].str();
				rv.push_back(new nRV(var, mean, deviation));
			}
			else
			{
				temp.push_back(line);
			}
		}
		file.close();
	}
	else
	{
		cout << "Could not open the file " << filename << endl;
	}
}

// The methods parses PDRH file
//
// @param full path to the inverted PDRH file
void FileParser::parse_pdrh_c(string filename)
{
	ifstream file;
	file.open(filename.c_str());
	smatch matches;
	if(file.is_open())
	{
		string line;
		while (getline(file, line))
		{
			temp_inv.push_back(line);
		}
		file.close();
	}
	else
	{
		cout << "Could not open the file " << filename << endl;
	}
}

// The method returns setting extracted from the
// setting file
std::map<string, string> FileParser::get_settings()
{
	return settings;
}

// The method return the list of independent random variables
vector<RV*> FileParser::get_rv()
{
	return rv;
}

// The method returns PDRH template of the problem
vector<string> FileParser::get_temp()
{
	return temp;
}

// The method returns PDRH template of the inverted problem
vector<string> FileParser::get_temp_inv()
{
	return temp_inv;
}
