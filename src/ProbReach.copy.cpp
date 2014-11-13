#include<regex>
#include<iostream>
#include<fstream>
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include<iomanip>
#include<fstream>
#include<math.h>
#include<time.h>
#include<omp.h>
#include<exception>
#include<typeinfo>
#include<unistd.h> 
#include<sys/types.h>
#include<signal.h>
#include "PartialSum.h"
#include "Integral.h"
#include "RVIntegral.h"
#include "MulRVIntegral.h"
#include "RV.h"
#include "nRV.h"
#include "DecisionProcedure.h"
#include "BoxFactory.h"
#include "FileParser.h"

using namespace std;
using namespace capd;

/*
double precision;
string model_file = "";
string model_file_complement = "";
string dReach_options = "";
vector<string> drh_template;
vector<string> drh_template_inverse;
bool verbose = false;
string settings_file_path = "";
double id = time(NULL);
*/

//for json output
/*
vector<DInterval> json_intervals;
vector<DInterval> json_partial_sums;
vector<DInterval> json_probability;
vector<double> json_operation_time;
vector<double> json_total_time;
vector<int> json_borel;
DInterval json_domain;
string json_filename;
string json_pdf;

DecisionProcedure dec_proc;
pid_t pid;
*/
/*
#ifdef _OPENMP
	omp_lock_t lock;
#endif
*/
//const regex normal_regex("(\\s)*(N)(\\s)*(\\()([-+]?[0-9]*.?[0-9]+)(\\s)*(,)(\\s)*([-+]?[0-9]*.?[0-9]+)(\\s)*(\\))(\\s)*([a-zA-Z][a-zA-Z0-9_]*)(;)(\\s)*");
//const regex uniform_reg_ex("(\\s)*(U)(\\s)*(\\()([-+]?[0-9]*.?[0-9]+)(\\s)*(,)(\\s)*([-+]?[0-9]*.?[0-9]+)(\\s)*(\\))(\\s)*([a-zA-Z][a-zA-Z0-9_]*)(;)(\\s)*");

/**
 * Takes name of pdrh template and return the drh
 * if rvIgnore is false then random variables are ignored
 */
 /*
void get_temp_from_file(string filepath, vector<string> &temp, vector<RV*> &rv)
{
	ifstream file;
	file.open(filepath.c_str());
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
		cout << "Could not open the file " << filepath << endl;
	}
}
*/

/**
 * Takes name of pdrh template and return the drh
 * if rvIgnore is false then random variables are ignored
 */
/*
void get_temp_from_file(string filepath, vector<string> &temp)
{
	ifstream file;
	file.open(filepath.c_str());
	smatch matches;
	if(file.is_open())
	{
		string line;
		while (getline(file, line))
		{
			temp.push_back(line);
		}
		file.close();
	}
	else
	{
		cout << "Could not open the file " << filepath << endl;
	}

}
*/
/*
void analize_flow(vector<string> &temp, vector<RV*> rv)
{
	const regex flow_regex(".*(flow).*(:).*");
	const regex init_regex(".*(init).*(:).*");
	const regex ode_regex(".*d/dt\\[([A-Za-z]+)\\]+.*");
	const regex init_line_regex(".*@[0-9]\\s*(\\(.*\\));\\s*");

	vector<string> flow_map;
	
	for(int i = 0; i < temp.size(); i++)
	{
		smatch matches;
		if(regex_match(temp.at(i), matches, flow_regex))
		{
			cout << temp.at(i) << endl;
		}
		if(regex_match(temp.at(i), matches, init_regex))
		{
			cout << temp.at(i) << endl;
		}
		if(regex_match(temp.at(i), matches, ode_regex))
		{
			if (find(flow_map.begin(), flow_map.end(), matches[1].str()) == flow_map.end())
			{
				flow_map.push_back(matches[1]);
			}
		}
		if(regex_match(temp.at(i), matches, init_line_regex))
		{
			cout << matches[1] << endl;
			cout << "(and " << matches[1] << " (my term));" << endl;
		}
	}


	cout << "Flow map" << endl;
	for(int i = 0; i < flow_map.size(); i++)
	{
		cout << flow_map.at(i) << endl;
	}

	for(int i = 0; i < rv.size(); i++)
	{
		if (find(flow_map.begin(), flow_map.end(), rv.at(i)->get_var()) != flow_map.end())
		{
			cout << rv.at(i)->get_var() << " is in the flow map" << endl; 
		}
		else
		{
			cout << rv.at(i)->get_var() << " should be added to the flow map" << endl; 
		}
	}
}
*/


/*
bool dReach(vector<RV> rv, string tempFilepath, vector<string> temp, string k, vector<Entry> x)
{
	//creating a unique name for drh file

	#ifdef _OPENMP
    	omp_set_lock(&lock);
 	#endif
	ostringstream tempStream;
	tempStream << tempFilepath;

	for (int i = 0; i < 1; i++)
	{
		tempStream << setprecision(16) << "_" << x.at(i).getSubInterval().leftBound() << "_" << x.at(i).getSubInterval().rightBound();
	}
	string drhFilepath = tempStream.str();
	ofstream drhFile;
	drhFile.open(string(drhFilepath + ".drh").c_str());
	if (drhFile.is_open())
	{
		//defining the random variables
		for(int i = 0; i < 1; i++)
		{
			drhFile << "#define " << rv.at(i).getVar() << "_a " << x.at(i).getSubInterval().leftBound() << endl;
			drhFile << "#define " << rv.at(i).getVar() << "_b " << x.at(i).getSubInterval().rightBound() << endl;
			drhFile << "[" << rv.at(i).getLeft() - (rv.at(i).getRight() - rv.at(i).getLeft()) * 10 << ", " << rv.at(i).getRight() + (rv.at(i).getRight() - rv.at(i).getLeft()) * 10<< "] " << rv.at(i).getVar() << ";" << endl;
		}
		ifstream drhTemplate;

		//adding the rest to the drh file
		for(int i = 0; i < temp.size(); i++)
		{
			drhFile << temp.at(i) << endl;
		}
		drhFile.close();
	}

	ostringstream callStream;
	string programOutput = "";
	if (!verbose)
	{
		programOutput = " > /dev/null";
	}
	
	callStream << "dReach -k " << k << " " << drhFilepath << ".drh -precision=" << width(x.at(0).getSubInterval()) / 1000 << programOutput << endl;
	#ifdef _OPENMP
    	omp_unset_lock(&lock);
 	#endif

	system((callStream.str()).c_str());

	//removing auxilary files

	#ifdef _OPENMP
    	omp_set_lock(&lock);
   	#endif
	if(remove(string(drhFilepath + ".drh").c_str()) != 0)
	{
		cout << "COULD NOT REMOVE FILE " << string(drhFilepath + ".drh") << endl;
	}
	if(remove(string(drhFilepath + ".preprocessed.drh").c_str()) != 0)
	{
		cout << "COULD NOT REMOVE FILE " << string(drhFilepath + ".preprocessed.drh") << endl;
	}
	if(remove(string(drhFilepath + "_" + k + "_0.smt2").c_str()) != 0)
	{
		cout << "COULD NOT REMOVE FILE " << string(drhFilepath + "_" + k + "_0.smt2") << endl;
	}

	string outputFilepath(drhFilepath + "_" + k + "_0.output");
	ifstream outputFile;
	outputFile.open(outputFilepath.c_str());

	if (outputFile.is_open())
	{

		string line;
		getline(outputFile, line);
		outputFile.close();
		if(remove(outputFilepath.c_str()) != 0)
		{
			cout << "COULD NOT REMOVE FILE " << outputFilepath << endl;
		}
		if (line == "sat")
		{
			
			#ifdef _OPENMP
    			omp_unset_lock(&lock);
   			#endif
			return true;
		}
		#ifdef _OPENMP
    		omp_unset_lock(&lock);
   		#endif
		return false;
	}
	else
	{
		cout << "COULD NOT OPEN THE FILE: " << outputFilepath << endl;
		#ifdef _OPENMP
    		omp_unset_lock(&lock);
   		#endif
    	exit(EXIT_FAILURE);
	}
}


void saveJSON()
{
	stringstream ss;
	ss << settingsFilePath << ".json";
	string filename = ss.str();
	
	ofstream JSON;
	JSON.open(filename.c_str());
	JSON.precision(16);

	JSON << "{ \"domain\": " << scientific << json_domain << "," << endl;
	JSON << "\"pdf\": " << json_pdf << "," << endl;
	JSON << "\"values\": [" << endl; 
	
	for(int i = 0; i < json_intervals.size() - 1; i++)
	{
		JSON << "{\"interval\": " << scientific << json_intervals.at(i) << ",";
		JSON << "\"partial_sum\": " << scientific << json_partial_sums.at(i) << ",";
		JSON << "\"probability\": " << scientific << json_probability.at(i) << ",";
		JSON << "\"precision\": " << scientific << width(json_probability.at(i)) << ",";
		JSON << "\"time\": " << json_operation_time.at(i) << ",";
		JSON << "\"total_time\": " << json_total_time.at(i) << ",";
		JSON << "\"borel\": " << json_borel.at(i) << "}," << endl;
	}

	JSON << "{\"interval\": " << json_intervals.at(json_intervals.size() - 1) << ",";
	JSON << "\"partial_sum\": " << json_partial_sums.at(json_intervals.size() - 1) << ",";
	JSON << "\"probability\": " << json_probability.at(json_intervals.size() - 1) << ",";
	JSON << "\"precision\": " << width(json_probability.at(json_intervals.size() - 1)) << ",";
	JSON << "\"time\": " << json_operation_time.at(json_intervals.size() - 1) << ",";
	JSON << "\"total_time\": " << json_total_time.at(json_intervals.size() - 1) << ",";
	JSON << "\"borel\": " << json_borel.at(json_intervals.size() - 1) << "}" << endl;

	JSON << "]}" << endl;
	JSON.close();
	
}
*/
/*
bool get_settings(string filename)
{
	ifstream settings_file;
	settings_file.open(filename.c_str());
	if (settings_file.is_open())
	{
		while (!settings_file.eof())
		{
			string line;
			getline(settings_file, line);
			if (line == "param:")
			{
				getline(settings_file, line);
				precision = atof(line.c_str());
				
			}
			if (line == "model:")
			{
				getline(settings_file, model_file);
				getline(settings_file, model_file_complement);
			}
						
			if (line == "dReach:")
			{
					while (!settings_file.eof())
					{
						getline(settings_file, line);
						smatch matches;
						regex depth_regex("(\\s)*([0-9]+)(\\s)*");
						if (regex_match(line, matches, depth_regex)) 
						{
							dReach_options += matches[0];
						}
					}
					break;
			}
		}
		settings_file.close();
		return true;		
	}
	return false;
}
*/

/*
int solveParallel(int argc, char *argv[])
{
	vector<RV> rv;
	vector<string> temp;
	vector<string> tempInv;

	getTempFromFile(modelFile, temp, rv);
	getTempFromFile(modelFileComplement, tempInv);
	
	if (rv.size() > 1)
	{
		cout << "WARNING!!! There are " << rv.size() << " random variables in the model. Only the first one will be considered" << endl;
	}
	
	double startTime = time(NULL);

	DInterval overIntg(1.0), underIntg(0.0);
	
	vector<Integral> integral;
	vector< vector<Entry> > vectors;
	
	Integral itg = Integral(rv.at(0), precision);
	DInterval I = itg.solve();
	overIntg =+ I.rightBound();
	vectors.push_back(itg.getEntries());
	integral.push_back(itg);
		
	vector< vector<Entry> > cartProduct = cartesianProduct(vectors);

	json_domain = DInterval(rv.at(0).getLeft(), rv.at(0).getRight());
	vector<Entry> extraEntries;
	
	//main loop	
	int counter = 0;
	#ifdef _OPENMP
    	omp_init_lock(&lock);
    	omp_set_num_threads(omp_get_max_threads() - 8);
 	#endif
    cout << "Required precision: " << scientific << precision << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| Probability interval         | Precision    | Time per iteration | Total time       |" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| [" << setprecision(12) << scientific << underIntg.leftBound() << ", " << overIntg.rightBound() << "] | " << overIntg.rightBound() - underIntg.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
	while (overIntg.rightBound() - underIntg.leftBound() > precision)
	{
		#pragma omp parallel
		{
			#pragma omp for schedule(dynamic)
			for (int i = 0; i < cartProduct.size(); i++)
			{
				double operationTime = time(NULL);
				if(verbose)
				{
					cout << counter << " of " << cartProduct.size()  << ") Interval: " << cartProduct.at(i).at(0).getSubInterval() << endl;
				}
				
				if (dReach(rv, modelFile, temp, dReachOptions, cartProduct.at(i)))
				{	
					if (dReach(rv, modelFileComplement, tempInv, dReachOptions, cartProduct.at(i)))
					{
						DInterval left(cartProduct.at(i).at(0).getSubInterval().leftBound(), cartProduct.at(i).at(0).getSubInterval().mid().rightBound());
						DInterval right(cartProduct.at(i).at(0).getSubInterval().mid().leftBound(), cartProduct.at(i).at(0).getSubInterval().rightBound());
						extraEntries.push_back(Entry(left, integral.at(0).calculateS(left)));
						extraEntries.push_back(Entry(right, integral.at(0).calculateS(right)));
    				}
					else
					{
						#pragma omp critical
						{
							underIntg += cartProduct.at(i).at(0).getPartialSum();
							counter++;
							cout << "| [" << setprecision(12) << scientific << underIntg.leftBound() << ", " << overIntg.rightBound() << "] | " << overIntg.rightBound() - underIntg.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - operationTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
							json_intervals.push_back(cartProduct.at(i).at(0).getSubInterval());
							json_partial_sums.push_back(cartProduct.at(i).at(0).getPartialSum());
							json_probability.push_back(DInterval(underIntg.leftBound(), overIntg.rightBound()));
							json_operation_time.push_back(time(NULL) - operationTime);
							json_total_time.push_back(time(NULL) - startTime);
							json_borel.push_back(1);
							saveJSON();
						}
					}
				}
				else
				{
					#pragma omp critical
					{
						overIntg -= cartProduct.at(i).at(0).getPartialSum();
						counter++;
						cout << "| [" << setprecision(12) << scientific << underIntg.leftBound() << ", " << overIntg.rightBound() << "] | " << overIntg.rightBound() - underIntg.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - operationTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;			
						json_intervals.push_back(cartProduct.at(i).at(0).getSubInterval());
						json_partial_sums.push_back(cartProduct.at(i).at(0).getPartialSum());
						json_probability.push_back(DInterval(underIntg.leftBound(), overIntg.rightBound()));
						json_operation_time.push_back(time(NULL) - operationTime);
						json_total_time.push_back(time(NULL) - startTime);
						json_borel.push_back(0);
						saveJSON();
					}
				}
			}
		}

		cartProduct.clear();
		
		
		#ifdef _OPENMP
	    	int numThreads = omp_get_max_threads();
	    #else
	    	int numThreads = 2;	
 		#endif
		
		while (extraEntries.size() < numThreads)
    	{
    		Entry entry = extraEntries.front();
    		extraEntries.erase(extraEntries.begin());
    		DInterval left(entry.getSubInterval().leftBound(), entry.getSubInterval().mid().rightBound());
			DInterval right(entry.getSubInterval().mid().leftBound(), entry.getSubInterval().rightBound());
			extraEntries.push_back(Entry(left, integral.at(0).calculateS(left)));
			extraEntries.push_back(Entry(right, integral.at(0).calculateS(right)));
    	}
		
		for (int i = 0; i < extraEntries.size(); i++)
		{
			vector<Entry> tmp;
			tmp.push_back(extraEntries.at(i));
			cartProduct.push_back(tmp);
		}
		
		extraEntries.clear();
		

	}
	#ifdef _OPENMP
    	omp_destroy_lock(&lock);
 	#endif

	saveJSON();

   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| Probability interval         | Precision    | Required precision | Total time       |" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| [" << setprecision(12) << scientific << underIntg.leftBound() << ", " << overIntg.rightBound() << "] | " << overIntg.rightBound() - underIntg.leftBound() << " | " << precision << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec |" << endl;
	cout << "|-------------------------------------------------------------------------------------|" << endl;

	return EXIT_SUCCESS;
}
*/

/*
int solveNotParallel(int argc, char *argv[])
{
	vector<RV> rv;
	vector<string> temp;
	vector<string> tempInv;

	getTempFromFile(modelFile, temp, rv);
	getTempFromFile(modelFileComplement, tempInv);
	
	if (rv.size() > 1)
	{
		cout << "WARNING!!! There are " << rv.size() << " random variables in the model. Only the first one will be considered" << endl;
	}
	
	double startTime = time(NULL);

	DInterval overIntg(1.0), underIntg(0.0), realIntg(0.0, 1.0), realIntgInf(0.0, 1.0);
	
	vector<Integral> integral;
	vector< vector<Entry> > vectors;
	vector<double> infError;
	
	Integral itg = Integral(rv.at(0), precision);
	DInterval I = itg.solve();
	overIntg =+ I.rightBound();
	vectors.push_back(itg.getEntries());
	integral.push_back(itg);
	infError.push_back(1 - I.leftBound());
		
	vector< vector<Entry> > cartProduct = cartesianProduct(vectors);
	
	vector<Entry> extraEntries;

	//main loop	
	int counter = 0;
    cout << "Required precision: " << scientific << precision << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| Probability interval         | Precision    | Time per iteration | Total time       |" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| [" << setprecision(12) << scientific << underIntg.leftBound() << ", " << overIntg.rightBound() << "] | " << overIntg.rightBound() - underIntg.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
	while (overIntg - underIntg > precision)
	{
			for (int i = 0; i < cartProduct.size(); i++)
			{
				double operationTime = time(NULL);
				if(verbose)
				{
					cout << counter << " of " << cartProduct.size()  << ") Interval: " << cartProduct.at(i).at(0).getSubInterval() << endl;
				}
				
				if (dReach(rv, modelFile, temp, dReachOptions, cartProduct.at(i)))
				{	
					if (dReach(rv, modelFileComplement, tempInv, dReachOptions, cartProduct.at(i)))
					{
						DInterval left(cartProduct.at(i).at(0).getSubInterval().leftBound(), cartProduct.at(i).at(0).getSubInterval().mid().rightBound());
						DInterval right(cartProduct.at(i).at(0).getSubInterval().mid().leftBound(), cartProduct.at(i).at(0).getSubInterval().rightBound());
						extraEntries.push_back(Entry(left, integral.at(0).calculateS(left)));
						extraEntries.push_back(Entry(right, integral.at(0).calculateS(right)));
    				}
					else
					{
						underIntg += cartProduct.at(i).at(0).getPartialSum();
						counter++;
						cout << "| [" << setprecision(12) << scientific << underIntg.leftBound() << ", " << overIntg.rightBound() << "] | " << overIntg.rightBound() - underIntg.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - operationTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
					}
				}
				else
				{
					overIntg -= cartProduct.at(i).at(0).getPartialSum();
					counter++;
					cout << "| [" << setprecision(12) << scientific << underIntg.leftBound() << ", " << overIntg.rightBound() << "] | " << overIntg.rightBound() - underIntg.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - operationTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;			
				}
			}

		cartProduct.clear();
		
		
    	int numThreads = 2;	
		
		while (extraEntries.size() < numThreads)
    	{
    		Entry entry = extraEntries.front();
    		extraEntries.erase(extraEntries.begin());
    		DInterval left(entry.getSubInterval().leftBound(), entry.getSubInterval().mid().rightBound());
			DInterval right(entry.getSubInterval().mid().leftBound(), entry.getSubInterval().rightBound());
			extraEntries.push_back(Entry(left, integral.at(0).calculateS(left)));
			extraEntries.push_back(Entry(right, integral.at(0).calculateS(right)));
    	}
		
		for (int i = 0; i < extraEntries.size(); i++)
		{
			vector<Entry> tmp;
			tmp.push_back(extraEntries.at(i));
			cartProduct.push_back(tmp);
		}
		
		extraEntries.clear();
		

	}

   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| Probability interval         | Precision    | Required precision | Total time       |" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| [" << setprecision(12) << scientific << underIntg.leftBound() << ", " << overIntg.rightBound() << "] | " << overIntg.rightBound() - underIntg.leftBound() << " | " << precision << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec |" << endl;
	cout << "|-------------------------------------------------------------------------------------|" << endl;

	return EXIT_SUCCESS;
}
*/

/*
void generate_json(vector <vector<PartialSum> > par_sums)
{
	ofstream JSON;
	JSON.open("/home/b2049657/ProbReach-dev/src/output.json");
	JSON.precision(16);

	JSON << "{ \"values\": ["; //<< endl; 
	
	for(int i = 0; i < par_sums.size() - 1; i++)
	{
		JSON << "{\"box\": {";// << endl;
		for(int j = 0; j < par_sums.at(i).size() - 1; j++)
		{
			JSON << "\"d" << j <<"\": " << par_sums.at(i).at(j).get_interval() << ",";
		}
		JSON << "\"d" << par_sums.at(i).size() - 1 <<"\": " << par_sums.at(i).at(par_sums.at(i).size() - 1).get_interval() << "}},";// << endl;
	}

	JSON << "{\"box\": {";// << endl;
	for(int j = 0; j < par_sums.at(par_sums.size() - 1).size() - 1; j++)
	{
		JSON << "\"d" << j <<"\": " << par_sums.at(par_sums.size() - 1).at(j).get_interval() << ",";
	}
	JSON << "\"d" << par_sums.at(par_sums.size() - 1).size() - 1 <<"\": " << par_sums.at(par_sums.size() - 1).at(par_sums.at(par_sums.size() - 1).size() - 1).get_interval() << "}}";// << endl;
	
	JSON << "]}";// << endl;
	JSON.close();
}
*/
/*
static void terminate(int sig)
{
	cout << "RECEIVED " << sig << endl;
	dec_proc.remove_aux_files();
	stringstream s;
	s << "kill -9 -" << getpid();
	system(s.str().c_str());
}
*/

ostream& operator<<(ostream& strm, Box& box)
{
	for(int i = 0; i < box.get_dimension_size() - 1; i++)
	{
		strm << box.get_interval_of(i) << "x";
	}
	strm << box.get_interval_of(box.get_dimension_size() - 1);
	
	return strm;
}

void branch_and_evaluate(char* argv[])
{
	FileParser file_parser(argv[1]);
	std::map<string, string> settings = file_parser.get_settings();
	vector<RV*> rv = file_parser.get_rv();
	vector<string> temp = file_parser.get_temp();
	vector<string> temp_inv = file_parser.get_temp_inv();

	MulRVIntegral mul_rv_integral = MulRVIntegral(rv, 0.1, atof(settings["precision"].c_str()));
	vector<Box> cart_prod = BoxFactory::calculate_cart_prod(mul_rv_integral.get_partial_sums());
	std::map<string, double> options = std::map<string, double>();
	DecisionProcedure dec_proc = DecisionProcedure(temp, temp_inv, rv, settings);
	DInterval P_lower(0.0);
	DInterval P_upper(2.0 - mul_rv_integral.get_value().leftBound());

    cout << getpid() << endl;
    vector<Box> mixed_boxes;

    int num_threads = 1;
	
    #ifdef _OPENMP
    	num_threads = omp_get_max_threads() - 8;
    	omp_set_num_threads(num_threads);
 	#endif

	while(P_upper.rightBound() - P_lower.leftBound() > atof(settings["precision"].c_str()))
	{
		#pragma omp parallel
		{
			#pragma omp for schedule(dynamic)
			for(int i = 0; i < cart_prod.size(); i++)
			{
				Box box = cart_prod.at(i);
				int is_borel = dec_proc.evaluate(box);
				if(is_borel == -1)
				{
					cout << box << setprecision(12) << " is not in B and P in [" << P_lower.leftBound() << "," << P_upper.rightBound() << "]" << endl;
					P_upper -= box.get_value();
				}
				if(is_borel == 1)
				{
					cout << box << setprecision(12) << " is in B and P in [" << P_lower.leftBound() << "," << P_upper.rightBound() << "]" << endl;
					P_lower += box.get_value();
				}
				if(is_borel == 0)
				{
					cout << box << setprecision(12) << " is a mixed box" << endl;
					mixed_boxes.push_back(box);
				}
			}
		}

		cart_prod.clear();

		while (mixed_boxes.size() < num_threads)
    	{
    		Box box = mixed_boxes.front();
    		mixed_boxes.erase(mixed_boxes.begin());
    		vector<Box> temp = BoxFactory::branch_box(box);
    		for(int i = 0; i < temp.size(); i++)
			{
				mixed_boxes.push_back(temp.at(i));
			}
    	}

		for(int i = 0; i < mixed_boxes.size(); i++)
		{
			cart_prod.push_back(mixed_boxes.at(i));
		}
		mixed_boxes.clear();
	}
	cout << setprecision(12) << "P in [" << P_lower.leftBound() << "," << P_upper.rightBound() << "]" << endl;
	
}

int main(int argc, char* argv[])
{
	branch_and_evaluate(argv);
	return EXIT_SUCCESS;
}




