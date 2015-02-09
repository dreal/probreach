#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include<sstream>
#include<iostream>
#include<iomanip>
#include<unistd.h> 
#include<sys/types.h>
#include<signal.h>
#include<omp.h>

#include "DecisionProcedure.h"
#include "PartialSum.h"
#include "RV.h"
#include "Box.h"
#include "FileParser.h"

using namespace std;
using namespace capd;

// Default constructor of the class
DecisionProcedure::DecisionProcedure()
{
	
}

DecisionProcedure::DecisionProcedure(pdrh_model model, option_type opt, string dreach_bin)
{
	this->model = model;
	this->opt = opt;
	this->dreach_bin = dreach_bin;
	generate_temp();
}

string DecisionProcedure::generate_drh(Box dd_box, Box rv_box, bool flag)
{
	stringstream s;

	if(flag)
	{
		s << get_current_dir_name() << scientific << setprecision(16) << "/phi_";
	}
	else
	{
		s << get_current_dir_name() << scientific << setprecision(16) << "/phi_C_";
	}

	for(int i = 0; i < dd_box.get_dimension_size(); i++)
	{
		s << dd_box.get_interval_of(i).leftBound() << "_" << dd_box.get_interval_of(i).rightBound() << "x";
	}

	for(int i = 0; i < rv_box.get_dimension_size(); i++)
	{
		s << rv_box.get_interval_of(i).leftBound() << "_" << rv_box.get_interval_of(i).rightBound() << "x";
	}
	
	string drh_filename_base = s.str();
	file_base.push_back(drh_filename_base);

	s << ".drh";
	string drh_filename = s.str();
	ofstream drh_file;
	drh_file.open(drh_filename.c_str());
	if (drh_file.is_open())
	{
		drh_file << scientific;
		for(int i = 0; i < dd_box.get_dimension_size(); i++)
		{
			drh_file << "#define " << dd_box.get_var_of(i) << " " << dd_box.get_interval_of(i).leftBound() << endl;
			drh_file << "#define " << dd_box.get_var_of(i) << " " << dd_box.get_interval_of(i).rightBound() << endl;
		}

		for(int i = 0; i < rv_box.get_dimension_size(); i++)
		{
			drh_file << "#define _" << rv_box.get_var_of(i) << "_a " << rv_box.get_interval_of(i).leftBound() << endl;
			drh_file << "#define _" << rv_box.get_var_of(i) << "_b " << rv_box.get_interval_of(i).rightBound() << endl;
			double radius = 100 * (model.rvs.at(i).get_domain().rightBound() - model.rvs.at(i).get_domain().leftBound());
			drh_file << "[" << model.rvs.at(i).get_domain().leftBound() - radius << ", " << model.rvs.at(i).get_domain().rightBound() + radius << "]" << model.rvs.at(i).get_var() << ";" << endl;
		}
			
		if(flag)
		{
			for(int i = 0; i < temp.size(); i++)
			{
				drh_file << temp.at(i) << endl;
			}
		}
		else
		{
			for(int i = 0; i < temp_c.size(); i++)
			{
				drh_file << temp_c.at(i) << endl;
			}
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
int DecisionProcedure::evaluate(Box dd_box, Box rv_box)
{
	double precision = opt.delta;
	string phi;
	string phi_c;
	if(rv_box.get_dimension_size() > 0)
	{
		precision = rv_box.get_min_width() / 1000;
	}
		
	#pragma omp critical
	{
		phi = generate_drh(dd_box, rv_box, true);
	}
	if(call_dreach(phi, precision))
	{
		if(rv_box.get_dimension_size() > 0)
		{
			precision = rv_box.get_min_width() / 1000;
		}
		#pragma omp critical
		{
			phi_c = generate_drh(dd_box, rv_box, false);
		}
		if(call_dreach(phi_c, precision))
		{
			//cout << phi << " sat" << endl;
			//cout << phi_c << " sat" << endl;
			//cout << rv_box.get_interval_of(0) << setprecision(12) << " is mixed" << endl;
			return 0;
		}
		else
		{
			//cout << rv_box.get_interval_of(0) << setprecision(12) << " is in B" << endl;
			//cout << phi << " sat" << endl;
			//cout << phi_c << " unsat" << endl;
			return 1;
		}
	}
	else
	{
		//cout << phi << " unsat" << endl;
		//cout << rv_box.get_interval_of(0) << setprecision(12) << " is not in B" << endl;
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
	
	s << dreach_bin << " -k " << opt.depth << " " << drh_filename_base << ".drh -precision=" << opt.delta << " > /dev/null" << endl;
	//s << "dReach -k " << opt.depth << " " << drh_filename_base << ".drh -precision=" << opt.delta << " > /dev/null" << endl;
	
	system(s.str().c_str());

	s.str("");
	s << drh_filename_base << "_" << opt.depth << "_0.output";
	ifstream output;
	output.open(s.str().c_str());

	if (output.is_open())
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
    	//remove_aux_files();
    	cout << "FAULT!!!" << endl;
    	exit(EXIT_FAILURE);
	}

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
	string preprocessed = filename_base + ".preprocessed.drh";
	s.str("");
	s << filename_base << "_" << opt.depth << "_0";
	string smt2 = s.str() + ".smt2";
	string output = s.str() + ".output";
	
	if(file_exists(drh.c_str())) remove(drh.c_str()); 
	if(file_exists(preprocessed.c_str())) remove(preprocessed.c_str());
	if(file_exists(smt2.c_str())) remove(smt2.c_str());
	if(file_exists(output.c_str())) remove(output.c_str());
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

void DecisionProcedure::generate_temp()
{
	ostringstream os;
	for(int i = 0; i < model.vars.size(); i++)
	{
		os << "[" << model.vars.at(i).range.leftBound() << ", " << model.vars.at(i).range.rightBound() << "]" << model.vars.at(i).name << ";" << endl;
	}

	temp.push_back(os.str());
	temp_c.push_back(os.str());
	os.str("");

	for(int i = 0; i < model.modes.size(); i++)
	{
		mode_type mode = model.modes.at(i);
		os << "{" << endl << "mode " << mode.id << ";" << endl;
		temp.push_back(os.str());
		temp_c.push_back(os.str());
		os.str("");

		if(mode.invts.size() > 0)
		{
			os << "invt:" << endl;
			for(int j = 0; j < mode.invts.size(); j++)
			{
				os << mode.invts.at(j) << endl;
			}
			temp.push_back(os.str());
			os.str("");
		}

		if(mode.invts_c.size() > 0)
		{
			os << "invt:" << endl;
			for(int j = 0; j < mode.invts_c.size(); j++)
			{
				os << mode.invts_c.at(j) << endl;
			}
			temp_c.push_back(os.str());
			os.str("");
		}

		os << "flow:" << endl;
		for(int j = 0; j < mode.flow.odes.size(); j++)
		{
			os << mode.flow.odes.at(j) << endl;
		}
		os << "jump:" << endl;
		for(int j = 0; j < mode.jumps.size(); j++)
		{
			os << mode.jumps.at(j).guard << "==>@" << mode.jumps.at(j).successor << mode.jumps.at(j).init << ";" << endl;
		}
		os << "}" << endl;
		temp.push_back(os.str());
		temp_c.push_back(os.str());
		os.str("");
	}

	os << "init:" << endl << "@" << model.init.mode << model.init.formula << ";" << endl << "goal:" << endl;
	temp.push_back(os.str());
	temp_c.push_back(os.str());
	os.str("");

	os << "@" << model.goal.mode << model.goal.formula << ";" << endl;
	temp.push_back(os.str());

	os.str("");

	os << "@" << model.goal_c.mode << model.goal_c.formula << ";" << endl;
	temp_c.push_back(os.str());
}