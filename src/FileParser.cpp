// FileParser class implements a parser for the
// files in PDRH format
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#include<string>
#include<sstream>
#include<unistd.h> 
#include<sys/types.h>
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<regex>
#include "BoxFactory.h"
#include "old_Box.h"
#include "PartialSum.h"
#include "FileParser.h"
#include "RV.h"
#include "DD.h"
//#include "nRV.h"

using namespace std;
using namespace capd;

// naive identification of nondeterminism in the model
bool FileParser::is_nondet()
{
	vector<var_type> v = model.vars;
	vector<mode_type> m = model.modes;
	for(int i = 0; i < m.size(); i++)
	{
		for(int j = 0; j < v.size(); j++)
		{
			if(strcmp(v.at(j).name.c_str(), "time") != 0)
			{
				if (std::find(m.at(i).flow.vars.begin(), m.at(i).flow.vars.end(), v.at(j).name) == m.at(i).flow.vars.end())
				{
					return true;
				}
			}
		}
	}
	return false;
}

// model type autodetection
int FileParser::auto_detect()
{
	if(model.rvs.size() > 0 || model.dds.size() > 0)
	{
		if(is_nondet())
		{
			//NPHA
			return 3;
		}
		else
		{
			//PHA
			return 2;
		}
	}
	else
	{
		//HA
		return 1;
	}
}


// Constructor of the class
//
// @param full path to the settings file
bool FileParser::file_exists(const char *filename)
{
	FILE* file;
	file = fopen(filename, "r");
	if(file != NULL)
	{
		fclose(file);
		return true;
	}
	else
	{
		return false;
	}
}

FileParser::FileParser(string filebase)
{

	string filename = filebase + ".pdrh";
	if(!file_exists(filename.c_str()))
	{
		cerr << "Invalid file path: " << filename << endl;
		exit(EXIT_FAILURE); 
	}
	
	string filename_prep = filebase + ".preprocessed.pdrh";

	stringstream s;
	
	char cur_dir[FILENAME_MAX];
	getcwd(cur_dir, sizeof(cur_dir));
	
	s << "sed \"s/\\/\\/.*//g\" " << filename << " | cpp -P -w | sed \"s/ //g\" > " << cur_dir << "/" << filename_prep;

	system(s.str().c_str());

	parse_pdrh(filename_prep);

	//autodetect model type here
	if(model.model_type == 0)
	{
		model.model_type = auto_detect();
		cout << "Model type autodetection: " << model.model_type << endl;
	}

	modify_flows();
	modify_init();

	for(auto it = model.param_syn.begin(); it != model.param_syn.end(); it++)
	{
		bool param_is_not_declared = true;
		for(int i = 0; i < model.params.size(); i++)
		{
			if(strcmp(it->first.c_str(), model.params.at(i).name.c_str()) == 0)
			{
				param_is_not_declared = false;
			}
		}
		if(param_is_not_declared)
		{
			cerr << "Parameter " << it->first << " was not declared in pdrh file" << endl;
			exit(EXIT_FAILURE);
		}
	}

	if(file_exists(filename_prep.c_str()))
	{
		remove(filename_prep.c_str());
	}
	else
	{
		cerr << "Problems occurred removing auxiliary files" << endl;
	}
}

// The methods parses PDRH file
//
// @param full path to the PDRH file
void FileParser::parse_pdrh(string filename)
{

	ifstream file;
	file.open(filename.c_str());
	smatch matches;
	
	if(file.is_open())
	{
		string line;

		while (getline(file, line))
		{
			// parsing model type
			if(regex_match(line, matches, regex("MODEL_TYPE\\((.*)\\)")))
			{
				string m_type = matches[1].str();
				if(strcmp(m_type.c_str(), string("HA").c_str()) == 0)
				{
					model.model_type = 1;
				}
				else if(strcmp(m_type.c_str(), string("PHA").c_str()) == 0)
				{
					model.model_type = 2;
				}
				else if(strcmp(m_type.c_str(), string("NPHA").c_str()) == 0)
				{
					model.model_type = 3;
				}
				//adopt to the format MODEL_TYPE(PSY;v0:0.1;alpha:0.01)
				else if (regex_match(m_type, matches, regex("PSY;+(.*)")))
				{
					model.model_type = 4;

					string declaration = matches[1].str();

					//vector<string> var;
					//vector<double> value;
					ostringstream os;
					string var = "";
					for(int i = 0; i < declaration.length(); i++)
					{
						if(declaration[i] == ':')
						{
							var = os.str();
							os.str("");
						}
						else
						{
							if((declaration[i] == ';'))
							{
								istringstream is(os.str());
								double v;
								is >> v;
								model.param_syn[var] = v;
								os.str("");
							}
							else
							{
								os << declaration[i];
								if((i == declaration.length() - 1))
								{
									istringstream is(os.str());
									double v;
									is >> v;
									model.param_syn[var] = v;
									os.str("");
								}
							}
						}
					}
				}
				else
				{
					cerr << "Unknown model type: " << m_type << " in " << filename << endl;
					exit(EXIT_FAILURE);
				}
			}
			// parsing variables
			else if(regex_match(line, matches, regex("\\[([-+]?[0-9]*.?[0-9]+),([-+]?[0-9]*.?[0-9]+)\\]([a-zA-Z][a-zA-Z0-9_]*);")))
			{
				var_type v;
				v.name = matches[3].str();
				v.range = DInterval(atof(matches[1].str().c_str()), atof(matches[2].str().c_str()));
				if(std::find(id_map.begin(), id_map.end(), v.name) != id_map.end()) 
				{
					cerr << "Variable " << v.name << " was already declared" << endl;
					exit(EXIT_FAILURE);
				}
				model.vars.push_back(v);
			}
			// parsing random parameters
			else if(regex_match(line, matches, regex("([A-Z]+)\\((.*)\\)([a-zA-Z][a-zA-Z0-9_]*);")))
			{
				if(std::find(id_map.begin(), id_map.end(), matches[3].str()) != id_map.end()) 
				{
					cerr << "Variable " << matches[3].str() << " was already declared" << endl;
					exit(EXIT_FAILURE);
				}
				parse_rv(matches[1].str(), matches[2].str(), matches[3].str());
			}
			// parsing modes
			else if(regex_match(line, regex("\\{")))
			{
				mode_type m;
				bool in_invt = false;
				bool in_invt_c = false;
				bool in_flow = false;
				bool in_jump = false;
				flow_type f;
				while(true)
				{
					if(strcmp(line.c_str(), string("}").c_str()) == 0)
					{
						break;
					}
					// parsing mode number
					if(regex_match(line, matches, regex("mode([1-9][0-9]*);")))
					{
						m.id = atoi(matches[1].str().c_str());
					}
					// parsing flow
					if(strcmp(line.c_str(), string("flow:").c_str()) == 0)
					{
						in_flow = true;
						in_invt = false;
						in_invt_c = false;
						in_jump = false;
					}
					// parsing odes
					if((in_flow) && (regex_match(line, matches, regex("d/dt\\[([A-Za-z][A-Za-z0-9_]*)\\]=.*;"))))
					{
						f.vars.push_back(matches[1].str());
						f.odes.push_back(matches[0].str());
					}
					// parsing jump
					if(strcmp(line.c_str(), string("jump:").c_str()) == 0)
					{
						in_flow = false;
						in_invt = false;
						in_invt_c = false;
						in_jump = true;
						m.flow = f;
					}
					// parsing jump condition
					if(in_jump)
					{
						if(regex_match(line, matches, regex("([0-9]*.?[0-9]+):(.*)==>@([1-9][0-9]*)(.*);")))
						{
							jump_type j;
							j.random = true;
							j.probability = atof(matches[1].str().c_str());
							j.guard = matches[2].str();
							j.successor = atoi(matches[3].str().c_str());
							j.init = matches[4].str();
							m.jumps.push_back(j);
						}
						else
						{
							if(regex_match(line, matches, regex("(.*)==>@([1-9][0-9]*)(.*);")))
							{
								jump_type j;
								j.random = false;
								j.probability = 1;
								j.guard = matches[1].str();
								j.successor = atoi(matches[2].str().c_str());
								j.init = matches[3].str();
								m.jumps.push_back(j);
							}
						}
					}
					// parsing invt_c:
					if(strcmp(line.c_str(), string("invt_c:").c_str()) == 0)
					{
						in_flow = false;
						in_invt = false;
						in_invt_c = true;
						in_jump = false;
						getline(file, line);
					}
					if(in_invt_c)
					{
						m.invts_c.push_back(line);
					}
					// parsing invt:
					if(strcmp(line.c_str(), string("invt:").c_str()) == 0)
					{
						in_flow = false;
						in_invt = true;
						in_invt_c = false;
						in_jump = false;
						getline(file, line);
					}
					if(in_invt)
					{
						m.invts.push_back(line);
					}
					getline(file, line);
				}
				model.modes.push_back(m);
			}
			// parsing init
			else if(strcmp(line.c_str(), string("init:").c_str()) == 0)
			{
				while(true)
				{
					getline(file, line);
					if(regex_match(line, matches, regex("@([1-9][0-9]*)(.*);")))
					{
						model.init.mode = atoi(matches[1].str().c_str());
						model.init.formula = matches[2].str();
						break;
					}
					if(regex_match(line, matches, regex("@([1-9][0-9]*)(.*)")))
					{
						model.init.mode = atoi(matches[1].str().c_str());
						stringstream init_stream;
						init_stream << matches[2].str();
						while(true)
						{
							getline(file, line);
							if(regex_match(line, matches, regex("(.*);")))
							{
								init_stream << matches[1].str();
								model.init.formula = init_stream.str();
								break;
							}
							else
							{
								init_stream << line;
							}
						}
						break;
					}
				}
			}
			// parsing goal
			else if(strcmp(line.c_str(), string("goal:").c_str()) == 0)
			{
				while(true)
				{
					getline(file, line);
					if(regex_match(line, matches, regex("@([1-9][0-9]*)(.*);")))
					{
						model.goal.mode = atoi(matches[1].str().c_str());
						model.goal.formula = matches[2].str();
						break;
					}
					if(regex_match(line, matches, regex("@([1-9][0-9]*)(.*)")))
					{
						model.goal.mode = atoi(matches[1].str().c_str());
						stringstream goal_stream;
						goal_stream << matches[2].str();
						while(true)
						{
							getline(file, line);
							if(regex_match(line, matches, regex("(.*);")))
							{
								goal_stream << matches[1].str();
								model.goal.formula = goal_stream.str();
								break;
							}
							else
							{
								goal_stream << line;
							}
						}
						break;
					}
				}
			}
			// parsing goal_c
			else if(strcmp(line.c_str(), string("goal_c:").c_str()) == 0)
			{
				while(true)
				{
					getline(file, line);
					if(regex_match(line, matches, regex("@([1-9][0-9]*)(.*);")))
					{
						model.goal_c.mode = atoi(matches[1].str().c_str());
						model.goal_c.formula = matches[2].str();
						break;
					}
					if(regex_match(line, matches, regex("@([1-9][0-9]*)(.*)")))
					{
						model.goal_c.mode = atoi(matches[1].str().c_str());
						stringstream goal_c_stream;
						goal_c_stream << matches[2].str();
						while(true)
						{
							getline(file, line);
							if(regex_match(line, matches, regex("(.*);")))
							{
								goal_c_stream << matches[1].str();
								model.goal_c.formula = goal_c_stream.str();
								break;
							}
							else
							{
								goal_c_stream << line;
							}
						}
						break;
					}
				}
			}
			else
			{
				cerr << "Syntax error in line: " << line << endl;
				exit(EXIT_FAILURE);
			}
		}
		file.close();

		if(model.model_type == 0)
		{
			model.model_type = auto_detect();
		}

	}
	else
	{
		cerr << "Could not open the file " << filename << endl;
		exit(EXIT_FAILURE);
	}
}

void FileParser::parse_rv(string notation, string declaration, string var)
{
	cmatch matches;
	if(strcmp(notation.c_str(), string("N").c_str()) == 0)
	{
		if(regex_match(declaration.c_str(), matches, regex("([-+]?[0-9]*.?[0-9]+),([-+]?[0-9]*.?[0-9]+)")))
		{
			double mean = atof(matches[1].str().c_str());
			double deviation = atof(matches[2].str().c_str());
			stringstream s;
			if(mean >= 0)
			{
				s 	<< "(1 / (" << deviation << " * sqrt(2 * 3.14159265359)) * exp(- (( " << var << " - " << mean 
				<<	") * (" << var << " - " << mean << ")) / (2 * " << deviation << " * " << deviation << ")))";
			}
			else
			{
				s 	<< "(1 / (" << deviation << " * sqrt(2 * 3.14159265359)) * exp(- (( " << var << " + " << -mean 
				<<	") * (" << var << " + " << -mean << ")) / (2 * " << deviation << " * " << deviation << ")))";
			}
			RV rv = RV(notation, var, s.str(), DInterval(mean - 3 * deviation, mean + 3 * deviation));
			model.rvs.push_back(rv);
		}
	}
	if(strcmp(notation.c_str(), string("U").c_str()) == 0)
	{
		if(regex_match(declaration.c_str(), matches, regex("([-+]?[0-9]*.?[0-9]+),([-+]?[0-9]*.?[0-9]+)")))
		{
			double left = atof(matches[1].str().c_str());
			double right = atof(matches[2].str().c_str());
			stringstream s;
			s 	<< "(1 / (" << (right - left) << "))";
			RV rv = RV(notation, var, s.str(), DInterval(left, right));
			model.rvs.push_back(rv);
		}
	}
	if(strcmp(notation.c_str(), string("DD").c_str()) == 0)
	{
		vector<double> arg;
		vector<double> value;
		ostringstream os;
		for(int i = 0; i < declaration.length(); i++)
		{
			if(declaration[i] == ':')
			{
				istringstream is(os.str());
				double a;
				is >> a;
				arg.push_back(a);
				os.str("");
			}
			else
			{
				if((declaration[i] == ','))
				{
					istringstream is(os.str());
					double v;
					is >> v;
					value.push_back(v);
					os.str("");
				}
				else
				{
					os << declaration[i];
					if((i == declaration.length() - 1))
					{
						istringstream is(os.str());
						double v;
						is >> v;
						value.push_back(v);
						os.str("");
					}
				}
			}	
		}
		DD dd = DD(var, arg, value);
		model.dds.push_back(dd);
	}
}

/*
vector<var_type> FileParser::get_vars()
{
	return vars;
}

vector<RV> FileParser::get_rvs()
{
	return rvs;
}

vector<mode_type> FileParser::get_modes()
{
	return modes;
}

init_type FileParser::get_init()
{
	return init;
}

goal_type FileParser::get_goal()
{
	return goal;
}

goal_type FileParser::get_goal_c()
{
	return goal_c;
}

vector<DD> FileParser::get_dds()
{
	return dds;
}

int FileParser::get_model_type()
{
	return model_type;
}
*/
pdrh_model FileParser::get_model()
{
	return model;
}

void FileParser::modify_flows()
{
	for(int i = 0; i < model.modes.size(); i++)
	{
		vector<string> flow_map = model.modes.at(i).flow.vars;
		for(int j = 0; j < model.vars.size(); j++)
		{
			if(std::find(flow_map.begin(), flow_map.end(), model.vars.at(j).name) == flow_map.end()) 
			{
				if(strcmp(model.vars.at(j).name.c_str(), string("time").c_str()) != 0)
				{
					model.modes.at(i).flow.vars.push_back(model.vars.at(j).name);
					model.modes.at(i).flow.odes.push_back(string("d/dt[" + model.vars.at(j).name + "]=0.0;"));
					// checking whether the parameter is not added
					bool flag_add = true;
					for(auto &par : model.params)
					{
						if(strcmp(model.vars.at(j).name.c_str(), par.name.c_str()) == 0)
						{
							flag_add = false;
						}
					}
					if(flag_add)
					{
						model.params.push_back(model.vars.at(j));
					}
				}
			}
		}
		for(int j = 0; j < model.rvs.size(); j++)
		{
			if(std::find(flow_map.begin(), flow_map.end(), model.rvs.at(j).get_var()) == flow_map.end()) 
			{
				model.modes.at(i).flow.vars.push_back(model.rvs.at(j).get_var());
				model.modes.at(i).flow.odes.push_back(string("d/dt[" + model.rvs.at(j).get_var() + "]=0.0;"));
			}
		}		
	}
}

void FileParser::modify_init()
{
	ostringstream os;
	os << "(and" << model.init.formula;
	for(int i = 0; i < model.rvs.size(); i++)
	{
		os 	<< "(" << model.rvs.at(i).get_var() << ">=_" << model.rvs.at(i).get_var() << "_a)" << "(" << model.rvs.at(i).get_var() << "<=_" << model.rvs.at(i).get_var() << "_b)";
	}
	for(int i = 0; i < model.params.size(); i++)
	{
		/*
		std::map<string,double>::iterator it;
		it = model.param_syn.find(model.params.at(i).name);
		if (it != model.param_syn.end())
		{
			os 	<< "(" << model.params.at(i).name << ">=_" << model.params.at(i).name << "_a)" << "(" << model.params.at(i).name << "<=_" << model.params.at(i).name << "_b)";
		}
		*/
		os 	<< "(" << model.params.at(i).name << ">=_" << model.params.at(i).name << "_a)" << "(" << model.params.at(i).name << "<=_" << model.params.at(i).name << "_b)";
	}
	os << ")";
	model.init.formula = os.str();
}
