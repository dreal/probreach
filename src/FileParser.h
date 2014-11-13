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

using namespace std;

// FileParser class declaration
class FileParser
{ 
	private:

		// Full path to PDRH model
		string model;

		// Full path to the inverted PDRH model
		string model_c;

		// PDRH template of the problem 
		vector<string> temp;

		// PDRH template of the inverted problem
		vector<string> temp_inv;

		// List of independent random variables
		vector<RV*> rv;

		// settings provided by the user containing
		// the computation precision, full paths to the 
		// PDRH files and verification depth
		std::map<string, string> settings;

		// The methods parses the settings provided as
		// an input for the application
		//
		// @param full path to the settings file
		void parse_settings(string);

		// The methods parses PDRH file
		//
		// @param full path to the PDRH file
		void parse_pdrh(string);

		// The methods parses PDRH file
		//
		// @param full path to the inverted PDRH file
		void parse_pdrh_c(string);

		// The methods performs all the necessary changes to
		// the "init" section of PDRH file
		void modify_init();

		// The methods performs all the necessary changes to
		// the "flow" sections of PDRH file
		void modify_flows();
		//void modify_jumps();
		
	public:
		
		// Constructor of the class
		//
		// @param full path to the settings file
		FileParser(string);

		// The method returns setting extracted from the
		// setting file
		std::map<string, string> get_settings();

		// The method return the list of independent random variables
		vector<RV*> get_rv();

		// The method returns PDRH template of the problem 
		vector<string> get_temp();

		// The method returns PDRH template of the inverted problem
		vector<string> get_temp_inv();
		
}; 
#endif  