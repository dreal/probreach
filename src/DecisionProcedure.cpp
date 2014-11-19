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

using namespace std;
using namespace capd;

// Default constructor of the class
DecisionProcedure::DecisionProcedure()
{
	
}

// Constructor of the class
//
// @param template of the problem,
// template of the inverted problem,
// settings used for the verification 
DecisionProcedure::DecisionProcedure(vector<string> pdrh_temp, vector<string> pdrh_temp_c, vector<RV*> rv, std::map<string, string> opt)
{
	this->pdrh_temp = pdrh_temp;
	this->pdrh_temp_c = pdrh_temp_c;
	this->opt = opt;
	this->rv = rv;
}

// The method get a Box and a flag as input parameters and 
// generates the DRH model for the problem if flag is true and 
// creates a DRH model for the inverted problem is the flag is false.
// The methods returns a full path to the generated DRH file.
//
// @param box from the domain of random variables, flag triggering
// generation of the inverse model
string DecisionProcedure::generate_drh(Box box, bool flag)
{
	stringstream s;

	if(flag)
	{
		s << get_current_dir_name() << setprecision(16) << "/phi_";
	}
	else
	{
		s << get_current_dir_name() << setprecision(16) << "/phi_C_";
	}

	for(int i = 0; i < box.get_dimension_size() - 1; i++)
	{
		s << box.get_interval_of(i).leftBound() << "_" << box.get_interval_of(i).rightBound() << "x";
	}
	s << box.get_interval_of(box.get_dimension_size() - 1).leftBound() << "_" << box.get_interval_of(box.get_dimension_size() - 1).rightBound() ;
	
	string drh_filename_base = s.str();
	file_base.push_back(drh_filename_base);

	s << ".drh";
	string drh_filename = s.str();
	ofstream drh_file;
	drh_file.open(drh_filename.c_str());
	if (drh_file.is_open())
	{
		for(int i = 0; i < box.get_dimension_size(); i++)
		{
			drh_file << "#define " << box.get_var_of(i) << "_a " << box.get_interval_of(i).leftBound() << endl;
			drh_file << "#define " << box.get_var_of(i) << "_b " << box.get_interval_of(i).rightBound() << endl;
			double radius = 100 * (rv.at(i)->get_domain().rightBound() - rv.at(i)->get_domain().leftBound());
			drh_file << "[" << rv.at(i)->get_domain().leftBound() - radius << ", " << rv.at(i)->get_domain().rightBound() + radius << "] " << box.get_var_of(i) << ";" << endl;
		}
		
		if(flag)
		{
			for(int i = 0; i < pdrh_temp.size(); i++)
			{
				drh_file << pdrh_temp.at(i) << endl;
			}
		}
		else
		{
			for(int i = 0; i < pdrh_temp_c.size(); i++)
			{
				drh_file << pdrh_temp_c.at(i) << endl;
			}
		}
		
		drh_file.close();
	}	
	return drh_filename_base;
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
	
	s << "dReach -k " << atof(opt["depth"].c_str()) << " " << drh_filename_base << ".drh -precision=" << precision << " > /dev/null" << endl;
	//s << "dReach -k " << opt["depth"] << " " << drh_filename_base << ".drh -precision=" << precision << endl;

	system(s.str().c_str());

	s.str("");
	s << drh_filename_base << "_" << atof(opt["depth"].c_str()) << "_0.output";
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
    	remove_aux_files();
    	cout << "FAULT!!!" << endl;
    	exit(EXIT_FAILURE);
	}

}

// The methods gets an arbitrary Box as an input parameter
// and return 1 if the indicator function over this box equals 1,
// -1 if indicator function equals to 0 and 0 if the box contains
// both values where the indicator function takes both values
//
// @param box from the domain of random variables. 
int DecisionProcedure::evaluate(Box box)
{
	double min_width;
	string phi;
	string phi_c;
	min_width = box.get_min_width() / 1000000;
	#pragma omp critical
	{
		phi = generate_drh(box, true);
	}
	if(call_dreach(phi, min_width))
	{
		min_width = box.get_min_width() / 1000000;
		#pragma omp critical
		{
			phi_c = generate_drh(box, false);
		}
		if(call_dreach(phi_c, min_width))
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
	s << filename_base << "_" << atof(opt["depth"].c_str()) << "_0";
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

