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
#ifdef _OPENMP
	#include<omp.h>
#endif
#include<exception>
#include<typeinfo>
#include<unistd.h> 
#include<sys/types.h>
#include<signal.h>
#include<sys/wait.h>
#include "PartialSum.h"
#include "Integral.h"
#include "RVIntegral.h"
#include "MulRVIntegral.h"
#include "RV.h"
#include "DecisionProcedure.h"
#include "BoxFactory.h"
#include "FileParser.h"

using namespace std;
using namespace capd;

double epsilon = 1e-03;
double inf_coeff = 1e-01;
string filename;
string dreach_bin = "dReach";
bool verbose = false;
bool visualize = false;
char* vis_par = "";
string dreach_options = "";
string dreal_options = "";
int max_num_threads = 1;
int num_threads = max_num_threads;
string probreach_version("1.1");

DInterval branch_and_evaluate(pdrh_model model, vector<Box> cart_prod, DInterval init_prob)
{
	double startTime = time(NULL);

	DecisionProcedure dec_proc = DecisionProcedure(dreach_bin, dreach_options, dreal_options);
	DInterval P_lower = init_prob.leftBound();
	DInterval P_upper = init_prob.rightBound();

    vector<Box> mixed_boxes;

	if(verbose)
	{	
	    cout << "|-------------------------------------------------------------------------------------|" << endl;
	    cout << "|-------------------------------BRANCH AND EVALUATE-----------------------------------|" << endl;
	    cout << "|-------------------------------------------------------------------------------------|" << endl;
	   	cout << "| Probability interval         | Precision    | Time per iteration | Total time       |" << endl;
	   	cout << "|-------------------------------------------------------------------------------------|" << endl;
	   	cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
	}

	vector<Box> json_intervals;
	vector<DInterval> json_probability;
	vector<double> json_operation_time;
	vector<double> json_total_time;
	vector<int> json_borel;

	//sorting initial partition
	sort(cart_prod.begin(), cart_prod.end(), BoxFactory::compare_boxes_des);

	while(true)
	{
		#pragma omp parallel
		{
			#pragma omp for schedule(dynamic)
			for(int i = 0; i < cart_prod.size(); i++)
			{
				double operationTime = time(NULL);
				Box box = cart_prod.at(i);
				// creating a model for the box above
				pdrh_model rv_model = model;
				stringstream s;
				for(int i = 0; i < box.get_dimension_size(); i++)
				{
					s << "#define _" << box.get_var_of(i) << "_a " << box.get_interval_of(i).leftBound() << endl;
					rv_model.defs.push_back(s.str());
					s.str("");
					s << "#define _" << box.get_var_of(i) << "_b " << box.get_interval_of(i).rightBound() << endl;
					rv_model.defs.push_back(s.str());
					s.str("");
					var_type var;
					var.name = model.rvs.at(i).get_var();
					double radius = 100 * (model.rvs.at(i).get_domain().rightBound() - model.rvs.at(i).get_domain().leftBound());
					var.range = DInterval(model.rvs.at(i).get_domain().leftBound() - radius, model.rvs.at(i).get_domain().rightBound() + radius);
					rv_model.vars.push_back(var);
				}
				// dReach is called here
				int is_borel = dec_proc.evaluate(rv_model, box.get_min_width() / 1000);
				// interpreting the result
				#pragma omp critical
				{
					if(is_borel == -1)
					{
						P_upper -= box.get_value();
						if(verbose)
						{
							cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - operationTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
						}
						if(visualize)
						{
							json_intervals.push_back(box);
							json_probability.push_back(DInterval(P_lower.leftBound(), P_upper.rightBound()));
							json_operation_time.push_back(time(NULL) - operationTime);
							json_total_time.push_back(time(NULL) - startTime);
							json_borel.push_back(0);
						}
					}
					if(is_borel == 1)
					{
						P_lower += box.get_value();
						if(verbose)
						{
							cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - operationTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
						}
						if(visualize)
						{
							json_intervals.push_back(box);
							json_probability.push_back(DInterval(P_lower.leftBound(), P_upper.rightBound()));
							json_operation_time.push_back(time(NULL) - operationTime);
							json_total_time.push_back(time(NULL) - startTime);
							json_borel.push_back(1);
						}
					}
					if(is_borel == 0)
					{
						if(model.model_type == 3)
						{
							if(box.get_max_width() > epsilon)
							{
								mixed_boxes.push_back(box);
							}
						}
						else
						{
							mixed_boxes.push_back(box);
						}
					}
				}
			}
		}

		cart_prod.clear();

		if(mixed_boxes.size() == 0)
		{
			break;
		}

		if(model.model_type == 2)
		{
			if(P_upper.rightBound() - P_lower.leftBound() <= epsilon)
			{
				break;
			}
		}

		int mixed_boxes_size = mixed_boxes.size();

		for(int i = 0; i < mixed_boxes_size; i++)
		{
			Box box = mixed_boxes.front();
    		mixed_boxes.erase(mixed_boxes.begin());
    		vector<Box> temp = BoxFactory::branch_box(box);
    		for(int j = 0; j < temp.size(); j++)
			{
				mixed_boxes.push_back(temp.at(j));
			}
		}

		if(mixed_boxes.size() < num_threads)
		{
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
		}
		
	   	sort(mixed_boxes.begin(), mixed_boxes.end(), BoxFactory::compare_boxes_des);

		for(int i = 0; i < mixed_boxes.size(); i++)
		{
			cart_prod.push_back(mixed_boxes.at(i));
		}
		mixed_boxes.clear();

	}
	if(verbose)
	{	
		cout << "|-------------------------------------------------------------------------------------|" << endl;
	   	cout << "|-------------------------------------------------------------------------------------|" << endl;
	   	cout << "| Probability interval         | Precision    | Required precision | Total time       |" << endl;
	   	cout << "|-------------------------------------------------------------------------------------|" << endl;
	   	cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << epsilon << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec |" << endl;
		cout << "|-------------------------------------------------------------------------------------|" << endl;
	}

	if(visualize)
	{
		int par_index;

		for(int i = 0; i < model.rvs.size(); i++)
		{
			if(strcmp(model.rvs.at(i).get_var().c_str(), vis_par) == 0)
			{
				par_index = i;
				break;
			}
		}

		string json_filename = filename + ".json";

		ofstream JSON;
		JSON.open(json_filename.c_str());
		JSON.precision(16);

		JSON << "{ \"domain\": " << scientific << model.rvs.at(par_index).get_domain() << "," << endl;
		JSON << "\"pdf\": ," << endl;
		JSON << "\"values\": [" << endl;

		for(int i = 0; i < json_intervals.size() - 1; i++)
		{
			JSON << "{\"interval\": " << scientific << json_intervals.at(i).get_dimension(par_index).get_interval() << ",";
			JSON << "\"partial_sum\": " << scientific << json_intervals.at(i).get_dimension(par_index).get_value() << ",";
			JSON << "\"probability\": " << scientific << json_probability.at(i) << ",";
			JSON << "\"precision\": " << scientific << width(json_probability.at(i)) << ",";
			JSON << "\"time\": " << json_operation_time.at(i) << ",";
			JSON << "\"total_time\": " << json_total_time.at(i) << ",";
			JSON << "\"borel\": " << json_borel.at(i) << "}," << endl;
		}

		JSON << "{\"interval\": " << scientific << json_intervals.at(json_intervals.size() - 1).get_dimension(par_index).get_interval() << ",";
		JSON << "\"partial_sum\": " << scientific << json_intervals.at(json_intervals.size() - 1).get_dimension(par_index).get_value() << ",";
		JSON << "\"probability\": " << scientific << json_probability.at(json_intervals.size() - 1) << ",";
		JSON << "\"precision\": " << scientific << width(json_probability.at(json_intervals.size() - 1)) << ",";
		JSON << "\"time\": " << json_operation_time.at(json_intervals.size() - 1) << ",";
		JSON << "\"total_time\": " << json_total_time.at(json_intervals.size() - 1) << ",";
		JSON << "\"borel\": " << json_borel.at(json_intervals.size() - 1) << "}" << endl;

		JSON << "]}" << endl;
		JSON.close();

		cout << "Generating JSON file. Saved to " << json_filename << endl;
	}

	return DInterval(P_lower.leftBound(), P_upper.rightBound());
}

void print_help()
{
	cout << endl;
	cout << "Help message:" << endl;
	cout << endl;
	cout << "	Run ./ProbReach <options> <model-file.pdrh> --dreach <dReach-options> --dreal <dReal-options>" << endl;
	cout << endl;
	cout << "options:" << endl;
	cout << "	-e <double> - length of probability interval or maximum length of the box (default 0.001)" << endl;
	cout << "	-d <double> - prescision used to call dReach (default 0.001)" << endl;
	cout << "	-l <string> - full path to dReach binary (default dReach)" << endl;
	cout << "	-t <int> - number of CPU cores (default " << max_num_threads << ") (max " << max_num_threads << ")" << endl;
	cout << "	-h/--help - help message" << endl;
	cout << "	--version - version of the tool" << endl;
	cout << "	--verbose - output computation details" << endl;
	cout << "	--visualize <char*> - visualize output for specified continuous random parameter" << endl;
	cout << "	--dreach - delimits dReach options (e.g. rechability depth)" << endl;
	cout << "	--dreal - delimits dReal options (e.g. precision, ode step)" << endl;
	cout << endl;
}

void print_version()
{
	cout << "ProbReach " << probreach_version << endl;
}

void parse_cmd(int argc, char* argv[])
{

	//no arguments are input
	if(argc < 2)
	{
		print_help();
		exit(EXIT_FAILURE);
	}

	//only one -h/--help or --version is provided
	if(argc == 2)
	{
		if((strcmp(argv[1], "-h") == 0) || (strcmp(argv[1], "--help") == 0)) 
		{
			print_help();
			exit(EXIT_SUCCESS);
		}
		else if((strcmp(argv[1], "--version") == 0))
		{
			print_version();
			exit(EXIT_SUCCESS);
		}
	}
	// parsing --dreach and --dreal options
	int opt_end = argc;
	stringstream s;
	cmatch matches;
	for(int i = 1; i < argc; i++)
	{
		//reached --dreach flag
		if(strcmp(argv[i], "--dreach") == 0)
		{
			//indicating the end of ProbReach options
			opt_end = i;
			while(true)
			{
				//reached the end of command line
				if(i == argc - 1) break;
				//next arg after --dreach flag
				i++;
				//reached --dreal flag
				if(strcmp(argv[i], "--dreal") == 0) break;
				s << argv[i] << " ";
			}
			//composing dReach options
			dreach_options = s.str();
		}
		//reached --dreal flag
		if(strcmp(argv[i], "--dreal") == 0)
		{
			//empty stream
			s.str("");
			while(true)
			{
				//reached the end of command line
				if(i == argc - 1) break;
				//next arg after --dreal flag
				i++;
				//if --dreach found while reading dReal options
				if(strcmp(argv[i], "--dreach") == 0)
				{
					cerr << "dReal options must be specified after dReach options" << endl;
					exit(EXIT_FAILURE);
				}
				s << argv[i] << " ";
			}
			//composing dReal options
			dreal_options = s.str();
		}

	}
	//parsing ProbReach options
	for(int i = 1; i < opt_end; i++)
	{
		//extracting a file name
		if(regex_match(argv[i], matches, regex("(.*/)*(.*).pdrh")))
		{
			filename = matches[1].str() + matches[2].str();
		}
		//help
		else if((strcmp(argv[i], "-h") == 0) || (strcmp(argv[i], "--help") == 0))
		{
			print_help();
		}
		//epsilon
		else if(strcmp(argv[i], "-e") == 0)
		{
			i++;
			istringstream is(argv[i]);
			is >> epsilon;
			if(epsilon <= 0)
			{
				cerr << "-e should be positive" << endl;
				exit(EXIT_FAILURE);
			}
		}
		//dReach binary
		else if(strcmp(argv[i], "-l") == 0)
		{
			i++;
			ostringstream os;
			os << argv[i] << "dReach";
			dreach_bin = os.str();
		}
		//verbose
		else if(strcmp(argv[i], "--verbose") == 0)
		{
			verbose = true;
		}
		//visualize
		else if(strcmp(argv[i], "--visualize") == 0)
		{
			visualize = true;
			i++;
			vis_par = argv[i];
		}
		//version
		else if(strcmp(argv[i], "--version") == 0)
		{
			print_version();
		}
		//number of cores
		else if(strcmp(argv[i], "-t") == 0)
		{
			i++;
			istringstream is(argv[i]);
			is >> num_threads;
			if(num_threads <= max_num_threads)
			{
				if(num_threads > 0)
				{	
					#ifdef _OPENMP
						omp_set_num_threads(num_threads);
					#endif
				}
				else
				{
					cerr << "Number of cores should be positive" << endl;
					exit(EXIT_FAILURE);
				}
			}
	    	else
	    	{
	    		cerr << "Max number of cores available is " << max_num_threads << ". You specified " << num_threads << endl;
				exit(EXIT_FAILURE);
	    	}
		}
		else
		{
			cerr << "Unrecognized option: " << argv[i] << endl;
			print_help();
			exit(EXIT_FAILURE);
		}
	}
	//case if filename is not specified
	if(strcmp(filename.c_str(), "") == 0)
	{
		cerr << "PDRH file is not specified" << endl;
		print_help();
		exit(EXIT_FAILURE);
	}
}

int main(int argc, char* argv[])
{
	// setting max number of threads by default
	#ifdef _OPENMP
		max_num_threads = omp_get_max_threads();
		num_threads = max_num_threads;
		omp_set_num_threads(num_threads);
	#endif

	// parse command line
	parse_cmd(argc, argv);

	// output input arguments
	if(verbose)
	{
		cout << "Input arguments:" << endl;
		cout << "epsilon = " << epsilon << endl;
		cout << "filename = " << filename << endl;
		cout << "number of cores used = " << num_threads << endl;
		if(visualize)
		{
			cout << "Parameter to visualize: " << vis_par << endl;
		}
		cout << "dReach version = " << dreach_bin << endl;
		cout << "dReach options: " << dreach_options << endl;
		cout << "dReal options: " << dreal_options << endl;
	}
	// parse *.pdrh filel
	FileParser file_parser(filename);
	pdrh_model model = file_parser.get_model();
	// checking if --visualize can be applied
	if(visualize)
	{
		if(model.dds.size() > 0)
		{
			cerr << "Failed to apply --visualize option. This options can be applied to models containing only continuous random parameters" << endl;
			exit(EXIT_FAILURE);
		}
		else
		{
			bool par_flag = false;
			for (int i = 0; i < model.rvs.size(); i++)
 			{
				if (strcmp(model.rvs.at(i).get_var().c_str(), vis_par) == 0)
				{
					par_flag = true;
					break;
				}
			}
			if (!par_flag)
			{
				cerr << "Failed to apply --visualize option. Parameter " << vis_par << " is not found in the list of continuous parameters in " << filename << endl;
				exit(EXIT_FAILURE);
			}
		}
	}

	if(verbose)
	{
		cout << "Model type = " << model.model_type << endl;
	}
	// main algorithm starts here
	vector<DInterval> P;
	DInterval P_final(0.0);
	vector<Box> dd_cart_prod;
	vector<Box> rv_cart_prod;
	// case when DDs are present
	if(model.dds.size() > 0)
	{
		// obtaining Cartesian product of DDs
		vector< vector<PartialSum> > dd_partial_sums;
		for(int i = 0; i < model.dds.size(); i++)
		{
			vector<PartialSum> temp_dd;
			for(int j = 0; j < model.dds.at(i).get_args().size(); j++)
			{
				temp_dd.push_back(PartialSum(model.dds.at(i).get_var(), "", DInterval(model.dds.at(i).get_args().at(j)), DInterval(model.dds.at(i).get_values().at(j))));
			}
			dd_partial_sums.push_back(temp_dd);
		}
		dd_cart_prod = BoxFactory::calculate_cart_prod(dd_partial_sums);
		// constructing initial probability vector
		for(int i = 0; i < dd_cart_prod.size(); i++)
		{
			DInterval temp_P = DInterval(1.0, 1.0);
			for(int j = 0; j < dd_cart_prod.at(i).get_dimensions().size(); j++)
			{
				temp_P *= dd_cart_prod.at(i).get_dimension(j).get_value();
			}
			P.push_back(temp_P);
		}
	}
	// calculating multiple integral for RVs
	DInterval init_prob;
	if(model.rvs.size() > 0)
	{
		MulRVIntegral mul_integral(model.rvs, inf_coeff, epsilon);
		rv_cart_prod = BoxFactory::calculate_cart_prod(mul_integral.get_partial_sums());
		init_prob = DInterval(0.0, 2.0 - mul_integral.get_value().leftBound());
	}
	//HA
	if(model.model_type == 1)
	{
		DecisionProcedure dec_proc(dreach_bin, dreach_options, dreal_options);
		int res = dec_proc.evaluate(model, -1);
		if(res == 1)
		{
			cout << "sat" << endl;
			P.push_back(DInterval(1.0, 1.0));
		}
		if(res == -1)
		{
			cout << "unsat" << endl;
			P.push_back(DInterval(0.0, 0.0));
		}
		if(res == 0)
		{
			cout << "undec" << endl;
			P.push_back(DInterval(0.0, 1.0));
		}
	}
	//PHA or NPHA
	else
	{
		// case when only RVs are present
		if(dd_cart_prod.size() == 0)
		{
			P.push_back(branch_and_evaluate(model, rv_cart_prod, init_prob));
		}
		// case when DDs are present
		else
		{
			for(int i = 0; i < dd_cart_prod.size(); i++)
			{
				// composing a model to evaluate
				pdrh_model dd_model = model;
				stringstream s;
				for (int j = 0; j < dd_cart_prod.at(i).get_dimension_size(); j++)
				{
					s << "#define " << dd_cart_prod.at(j).get_var_of(j) << " " << dd_cart_prod.at(j).get_interval_of(j).leftBound();
					dd_model.defs.push_back(s.str());
					s.str("");
				}
				// case	when both RVs and DDs are present
				if (rv_cart_prod.size() > 0)
				{
					P.at(i) *= branch_and_evaluate(dd_model, rv_cart_prod, init_prob);
				}
				// case when only DDs are present
				else
				{
					DecisionProcedure dec_proc(dreach_bin, dreach_options, dreal_options);
					int res = dec_proc.evaluate(dd_model, -1);
					if (res == 1)
					{
						P.at(i) *= DInterval(1.0);
					}
					if (res == -1)
					{
						P.at(i) *= DInterval(0.0);
					}
					if (res == 0)
					{
						P.at(i) *= DInterval(0.0, 1.0);
					}
				}
				cout << scientific << "P(" << dd_cart_prod.at(i) << ") = " << setprecision(16) << P.at(i) << endl;
			}
		}
	}
	// calculating final result
	for(int i = 0; i < P.size(); i++)
	{
		P_final += P.at(i);
	}
	// outputting final result
	cout << "P = " << scientific << setprecision(16) << P_final << endl;
	return EXIT_SUCCESS;
}






