#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include<cstring>
#include<sstream>
#include<iostream>
#include<iomanip>
#include<unistd.h> 
#include<sys/types.h>
#include<signal.h>

#ifdef _OPENMP
	#include<omp.h>
#endif

#include "DecisionProcedure.h"
#include "PartialSum.h"
#include "RV.h"
#include "Box.h"
#include "FileParser.h"

using namespace std;
using namespace capd;

DecisionProcedure::DecisionProcedure(string dreach_bin, string dreach_options, string dreal_options)
{
	this->dreach_bin = dreach_bin;
	this->dreach_options = dreach_options;
	this->dreal_options = dreal_options;
}

string DecisionProcedure::generate_drh(pdrh_model model, bool flag)
{

	//building a filenmae for .drh file
	stringstream s;
	#ifdef _OPENMP
		thread_num = omp_get_thread_num();
	#endif
	char cur_dir[FILENAME_MAX];
	getcwd(cur_dir, sizeof(cur_dir));
	s << cur_dir << "/phi";
	if(!flag)
	{
		s << "C";
	}
	s << thread_num;
	string drh_filename_base = s.str();
	file_base.push_back(drh_filename_base);
	s << ".drh";
	string drh_filename = s.str();

	//start composing a file
	ofstream drh_file;
	drh_file.open(drh_filename.c_str());
	if (drh_file.is_open())
	{
		for(int i = 0; i < model.defs.size(); i++)
		{
			drh_file << model.defs.at(i) << endl;
		}

		for(int i = 0; i < model.vars.size(); i++)
		{
			drh_file << model.vars.at(i).range << model.vars.at(i).name << ";" << endl;
		}

		for(int i = 0; i < model.modes.size(); i++)
		{
			mode_type mode = model.modes.at(i);
			drh_file << "{" << endl << "mode " << mode.id << ";" << endl;

			if(flag)
			{
				if (mode.invts.size() > 0)
				{
					drh_file << "invt:" << endl;
					for (int j = 0; j < mode.invts.size(); j++)
					{
						drh_file << mode.invts.at(j) << endl;
					}
				}
			}
			else
			{
				if (mode.invts_c.size() > 0)
				{
					drh_file << "invt:" << endl;
					for (int j = 0; j < mode.invts_c.size(); j++)
					{
						drh_file << mode.invts_c.at(j) << endl;
					}
				}
			}

			drh_file << "flow:" << endl;
			for(int j = 0; j < mode.flow.odes.size(); j++)
			{
				drh_file << mode.flow.odes.at(j) << endl;
			}
			drh_file << "jump:" << endl;
			for(int j = 0; j < mode.jumps.size(); j++)
			{
				drh_file << mode.jumps.at(j).guard << "==>@" << mode.jumps.at(j).successor << mode.jumps.at(j).init << ";" << endl;
			}
			drh_file << "}" << endl;
		}

		drh_file << "init:" << endl << "@" << model.init.mode << model.init.formula << ";" << endl << "goal:" << endl;

		if(flag)
		{
			drh_file << "@" << model.goal.mode << model.goal.formula << ";" << endl;
		}
		else
		{
			drh_file << "@" << model.goal_c.mode << model.goal_c.formula << ";" << endl;
		}
		drh_file.close();
	}
	return drh_filename_base;
}

// The methods gets an arbitrary Box as an input parameter
// and return 1 if the indicator function over this box equals 1,
// -1 if indicator function equals to 0 and 0 if the box contains
// both values where the indicator function takes both values
//
// @param box from the domain of random variables.

int DecisionProcedure::evaluate(pdrh_model model, double precision)
{
	string phi;
	string phi_c;

	#pragma omp critical
	{
		phi = generate_drh(model, true);
	}
	if(call_dreach(phi, precision))
	{
		#pragma omp critical
		{
			phi_c = generate_drh(model, false);
		}
		if(call_dreach(phi_c, precision))
		{
			return 0;
		}
		else
		{
			return 1;
		}
	}
	else
	{
		return -1;
	}
}


// The method gets a full path to the DRH model and a precision
// which are then used to call dReach. The method returns true
// if dReach returns "sat" and false if dReach returns "unsat".
//
// @param DRH filename, precision used by dReach for verifying
// the model
bool DecisionProcedure::call_dreach(string drh_filename_base, double precision)
{
	stringstream s;
	s << dreach_bin << " " << dreach_options << " " << drh_filename_base << ".drh " << dreal_options;

	if(precision > 0)
	{
		s << " --precision=" << precision;
	}
	s << " > /dev/null" << endl;

	int res = system(s.str().c_str());

	//remove_aux_file(drh_filename_base);

	if(!WIFEXITED(res))
	{
		cerr << "Error occured calling dReach" << endl;
		exit(EXIT_FAILURE);
	}

	switch(WEXITSTATUS(res))
	{
		case 51:
			return true;
		case 52:
			return false;
		default:
			cerr << "Unrecognized dReach exit status: " << WEXITSTATUS(res) << endl;
			cerr << "Try using -z dReach option" << endl;
			exit(EXIT_FAILURE);
	}

	/*
	ADD A FEATURE IN DREACH FOR WRITING TH ~E RESULT TO THE FILE phi_tread_num.output
	s.str("");
	s << drh_filename_base << "_" << opt.k << "_0.output";
	ifstream output;
	output.open(s.str().c_str());

	if(output.is_open())
	{
		string line;
		getline(output, line);
		output.close();
		if (line == "sat")
		{
    		remove_aux_file(drh_filename_base);
			return true;
		}
    	remove_aux_file(drh_filename_base);
		return false;
	}
	else
	{
    	remove_aux_files();
    	cout << "Couldn't open the file " << s.str() << endl;
    	exit(EXIT_FAILURE);
	}
	*/

}

// The method returns the list of the auxiliary filenames
vector<string> DecisionProcedure::get_file_base()
{
	return file_base;
}

// The method gets a name of the file as a parameter and returns
// true  if the file exists and false otherwise
bool DecisionProcedure::file_exists(const char *filename)
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

// The method removes auxiliary file
//
// @param filename base
void DecisionProcedure::remove_aux_file(string filename_base)
{
	stringstream s;
	string drh = filename_base + ".drh";
	//string preprocessed = filename_base + ".preprocessed.drh";
	//s.str("");
	//s << filename_base << "_" << opt.k << "_0";
	//string smt2 = s.str() + ".smt2";
	//string output = s.str() + ".output";
	
	if(file_exists(drh.c_str())) remove(drh.c_str());
	//if(file_exists(preprocessed.c_str())) remove(preprocessed.c_str());
	//if(file_exists(smt2.c_str())) remove(smt2.c_str());
	//if(file_exists(output.c_str())) remove(output.c_str());
}

// The method removes all the auxiliary files generated by dReach 
void DecisionProcedure::remove_aux_files()
{
	stringstream s;
	for(int i = 0; i < file_base.size(); i++)
	{
		remove_aux_file(file_base.at(i));
	}
	file_base.clear();
}
