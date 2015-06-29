// FileParser class implements a parser for the
// files in PDRH format
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#ifndef FILEPARSER_H  
#define FILEPARSER_H 
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include "PartialSum.h"
#include "Box.h"
#include "RV.h"
#include "DD.h"

using namespace std;

struct var_type
{
	string name;
	DInterval range;
};

struct flow_type
{
	vector<string> vars;
	vector<string> odes;
};

struct jump_type
{
	string guard;
	int successor;
	string init;
	bool random;
	double probability;
};

struct mode_type
{
	int id;
	vector<string> invts;
	vector<string> invts_c;
	flow_type flow;
	vector<jump_type> jumps;
};

struct init_type
{
	int mode;
	string formula;
};

struct goal_type
{
	int mode;
	string formula;
};

struct pdrh_model
{
	// 0 - AUTO DEFINITION
	// 1 - HA
	// 2 - PHA
	// 3 - NPHA
	// 4 - PSY
	int model_type = 0;
	vector<string> defs;
	vector<var_type> vars;
	vector<var_type> params;
	std::map<string, double> param_syn;
	vector<RV> rvs;
	vector<DD> dds;
	vector<mode_type> modes;
	init_type init;
	goal_type goal;
	goal_type goal_c;
};

// FileParser class declaration
class FileParser
{ 
	private:

		vector<string> id_map;

		pdrh_model model;

		// The methods parses PDRH file
		//
		// @param full path to the PDRH file
		void parse_pdrh(string);

		void parse_rv(string, string, string);

		void modify_flows();

		void modify_init();

		bool is_nondet();

		int auto_detect();
		
	public:

		// Constructor of the class
		//
		// @param full path to the settings file
		FileParser(string);

		bool file_exists(const char *);

		/*
		vector<var_type> get_vars();
		
		vector<RV> get_rvs();

		vector<DD> get_dds();
		
		vector<mode_type> get_modes();

		init_type get_init();

		goal_type get_goal();

		goal_type get_goal_c();

		int get_model_type();
		*/

		pdrh_model get_model();



}; 
#endif  