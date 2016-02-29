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
#include "CSVParser.h"
#include<capd/dynsys/OdeTraits.h>
#include "box.h"
#include "measure.h"
#include "box_factory.h"
#include "version.h"
#include "pugixml.hpp"
#include "model.h"
#include "pdrh_config.h"
#include "solver/dreal_wrapper.h"
#include "decision_procedure.h"

extern "C"
{
#include "../build/release/pdrhparser.h"
}

using namespace capd;
using namespace std;

double epsilon = 1e-03;
double inf_coeff = 1e-01;
double max_nondet = 1e-03;
string filename;
string dreach_bin = "dReach";
string solver_bin = "";
string solver_opt = "";
bool verbose = false;
bool visualize = false;
char* vis_par = "";
string dreach_options = "";
string dreal_options = "";
int max_num_threads = 1;
int num_threads = max_num_threads;
string probreach_version("1.2");
double series_noise = 1;
string series_filename;
bool prepartition_flag = false;
bool guided = false;
bool xml_output_flag = false;
pugi::xml_document xml_output;
bool merge_flag = false;

extern "C" int yyparse();
extern "C" FILE *yyin;

int evaluate_ha(pdrh_model model)
{
	//cout << "Evaluate HA" << endl;
	DecisionProcedure dec_proc(dreach_bin, dreach_options, dreal_options);
	//cout << "Before decision procedure" << endl;
	//vector<old_Box> result = dec_proc.evaluate_guided(model, -1);
	//cout << "Evaluated HA" << endl;
	/*
	if(result.at(0).get_dimension_size() == 0)
	{
		return -1;
	}
	else
	{
		if(result.at(1).get_dimension_size() == 0)
		{
			return 1;
		}
		else
		{
			return 0;
		}
	}
	 */
	return dec_proc.evaluate(model, -1);
}

DInterval branch_and_evaluate(pdrh_model model, vector<old_Box> cart_prod, DInterval init_prob)
{
	double startTime = time(NULL);

	DecisionProcedure dec_proc = DecisionProcedure(dreach_bin, dreach_options, dreal_options);
	DInterval P_lower = init_prob.leftBound();
	DInterval P_upper = init_prob.rightBound();

    vector<old_Box> mixed_boxes;

	if(verbose)
	{
	    cout << "|-------------------------------------------------------------------------------------|" << endl;
	    cout << "|-------------------------------BRANCH AND EVALUATE-----------------------------------|" << endl;
	    cout << "|-------------------------------------------------------------------------------------|" << endl;
	   	cout << "| Probability interval         | Precision    | Time per iteration | Total time       |" << endl;
	   	cout << "|-------------------------------------------------------------------------------------|" << endl;
	   	cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
	}

	vector<old_Box> json_intervals;
	vector<DInterval> json_probability;
	vector<double> json_operation_time;
	vector<double> json_total_time;
	vector<int> json_borel;

	//sorting initial partition
	sort(cart_prod.begin(), cart_prod.end(), BoxFactory::compare_boxes_des);

	vector<PartialSum> nondet_intervals;
	for(int i = 0; i < model.params.size(); i++)
	{
		nondet_intervals.push_back(PartialSum(model.params.at(i).name, "1", model.params.at(i).range));
	}

	vector<old_Box> n_boxes;
	if(nondet_intervals.size() > 0)
	{
		n_boxes.push_back(old_Box(nondet_intervals));
	}

	// fix later
	std::map<old_Box,DInterval> P_map;
	P_map[n_boxes.at(0)] = init_prob;

	cout << "Probability map:" << endl;
	for(auto it = P_map.begin(); it != P_map.end(); it++)
	{
		cout << "P(" << it->first << ")=" << it->second << endl;
	}

	//P_map.erase(nondet_domain);
	//cout << "Is empty: " << P_map.empty() << endl;

	if(n_boxes.size() > 0)
	{
		stringstream s;
		for(int i = 0; i < n_boxes.at(0).get_dimension_size(); i++)
		{
			s << "#define _" << n_boxes.at(0).get_var_of(i) << "_a " << n_boxes.at(0).get_interval_of(i).leftBound() << endl;
			model.defs.push_back(s.str());
			s.str("");
			s << "#define _" << n_boxes.at(0).get_var_of(i) << "_b " << n_boxes.at(0).get_interval_of(i).rightBound() << endl;
			model.defs.push_back(s.str());
			s.str("");
		}
	}

	while(true)
	{
		#pragma omp parallel
		{
			#pragma omp for schedule(dynamic)
			for(int j = 0; j < cart_prod.size(); j++)
			{
				double operationTime = time(NULL);
				old_Box box = cart_prod.at(j);
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
				vector<old_Box> result = dec_proc.evaluate_guided(rv_model, box.get_min_width() / 1000);
				int is_borel = 0;
				if(result.at(0).get_dimension_size() == 0)
				{
					is_borel = -1;
				}
				else
				{
					if(result.at(1).get_dimension_size() == 0)
					{
						is_borel = 1;
					}
				}

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
			old_Box box = mixed_boxes.front();
    		mixed_boxes.erase(mixed_boxes.begin());
    		vector<old_Box> temp = BoxFactory::branch_box(box);
    		for(int j = 0; j < temp.size(); j++)
			{
				mixed_boxes.push_back(temp.at(j));
			}
		}

		if(mixed_boxes.size() < num_threads)
		{
			while (mixed_boxes.size() < num_threads)
	    	{
	    		old_Box box = mixed_boxes.front();
	    		mixed_boxes.erase(mixed_boxes.begin());
	    		vector<old_Box> temp = BoxFactory::branch_box(box);

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

std::map<old_Box, DInterval> branch_and_evaluate_nondet(pdrh_model model, vector<old_Box> cart_prod, DInterval init_prob)
{

	DecisionProcedure dec_proc = DecisionProcedure(dreach_bin, dreach_options, dreal_options);
	DInterval P_lower = init_prob.leftBound();
	DInterval P_upper = init_prob.rightBound();

	vector<old_Box> mixed_boxes, mixed_n_boxes;

	//sorting initial partition
	sort(cart_prod.begin(), cart_prod.end(), BoxFactory::compare_boxes_des);

	vector<PartialSum> nondet_intervals;
	for(int i = 0; i < model.params.size(); i++)
	{
		nondet_intervals.push_back(PartialSum(model.params.at(i).name, "1", model.params.at(i).range));
	}

	vector<old_Box> n_boxes;
	if(nondet_intervals.size() > 0)
	{
		n_boxes.push_back(old_Box(nondet_intervals));
	}

	// fix later
	std::map<old_Box,DInterval> P_map, P_result;
	P_map[n_boxes.at(0)] = init_prob;

	std::map<old_Box, vector<old_Box>> partition_map;
	partition_map[n_boxes.at(0)] = cart_prod;

	while(!P_map.empty())
	{
		for(int k = 0; k < n_boxes.size(); k++)
		{
			/*
			cout << "Partition map:" << endl;
			for (auto it = partition_map.begin(); it != partition_map.end(); it++)
			{
				cout << setprecision(5) << scientific << it->first << endl;
				vector<old_Box> tmp_box_vector = it->second;
				for(int i = 0; i < tmp_box_vector.size(); i++)
				{
					cout << i << ") " << tmp_box_vector.at(i) << endl;
				}
			}
			*/
			pdrh_model nondet_model = model;
			cout << "Intermediate map:" << endl;
			for (auto it = P_map.begin(); it != P_map.end(); it++)
			{
				cout << setprecision(5) << scientific << "P(" << it->first << ") = " << it->second << " | " << width(it->second) << endl;
			}

			// modifying the model to handle nondeterministic parameters
			stringstream s;
			for (int i = 0; i < n_boxes.at(k).get_dimension_size(); i++)
			{
				s << "#define _" << n_boxes.at(k).get_var_of(i) << "_a " << n_boxes.at(k).get_interval_of(i).leftBound() << endl;
				nondet_model.defs.push_back(s.str());
				s.str("");
				s << "#define _" << n_boxes.at(k).get_var_of(i) << "_b " << n_boxes.at(k).get_interval_of(i).rightBound() << endl;
				nondet_model.defs.push_back(s.str());
				s.str("");
			}

			P_lower = P_map[n_boxes.at(k)].leftBound();
			P_upper = P_map[n_boxes.at(k)].rightBound();
			//cout << "Current nondet box: " << n_boxes.at(k) << endl;
			//cout << "---------------------------------" << endl;
			for (int j = 0; j < partition_map[n_boxes.at(k)].size(); j++)
			{
				old_Box box = partition_map[n_boxes.at(k)].at(j);
				// creating a model for the box above
				pdrh_model rv_model = nondet_model;
				// modifying the model to handle random parameters
				stringstream s;
				for (int i = 0; i < box.get_dimension_size(); i++)
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
				vector <old_Box> result = dec_proc.evaluate_guided(rv_model, box.get_min_width() / 1000);
				int is_borel = 0;
				if (result.at(0).get_dimension_size() == 0)
				{
					is_borel = -1;
				}
				else
				{
					if (result.at(1).get_dimension_size() == 0)
					{
						is_borel = 1;
					}
				}

				// interpreting the result
				#pragma omp critical
				{
					switch (is_borel)
					{
						case -1:
							P_upper -= box.get_value();
							/*
							if (verbose)
							{
								cout << setprecision(5) << scientific << "P(" << n_boxes.at(k) << ") = [" <<
								P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " <<
								P_upper.rightBound() - P_lower.leftBound() << endl;
							}
							*/
							break;

						case 1:
							P_lower += box.get_value();
							/*
							if (verbose)
							{
								cout << setprecision(5) << scientific << "P(" << n_boxes.at(k) << ") = [" <<
								P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " <<
								P_upper.rightBound() - P_lower.leftBound() << endl;
							}
							*/
							break;

						case 0:
							mixed_boxes.push_back(box);
							break;
					}
				}
			}
			//cout << "---------------------------------" << endl;

			P_map.erase(n_boxes.at(k));
			if (P_upper.rightBound() - P_lower.leftBound() <= epsilon)
			{
				P_result[n_boxes.at(k)] = DInterval(P_lower.leftBound(), P_upper.rightBound());
			}
			else
			{
				vector<old_Box> n_branch = BoxFactory::branch_box(n_boxes.at(k));
				for (int i = 0; i < n_branch.size(); i++)
				{
					P_map[n_branch.at(i)] = DInterval(P_lower.leftBound(), P_upper.rightBound());
					mixed_n_boxes.push_back(n_branch.at(i));
				}

				//cart_prod.clear();
				// branching of mixed boxes
				int mixed_boxes_size = mixed_boxes.size();
				for (int i = 0; i < mixed_boxes_size; i++)
				{
					old_Box box = mixed_boxes.front();
					mixed_boxes.erase(mixed_boxes.begin());
					vector <old_Box> temp = BoxFactory::branch_box(box);
					for (int j = 0; j < temp.size(); j++)
					{
						mixed_boxes.push_back(temp.at(j));
					}
				}

				if (mixed_boxes.size() < num_threads)
				{
					while (mixed_boxes.size() < num_threads)
					{
						old_Box box = mixed_boxes.front();
						mixed_boxes.erase(mixed_boxes.begin());
						vector <old_Box> temp = BoxFactory::branch_box(box);

						for (int i = 0; i < temp.size(); i++)
						{
							mixed_boxes.push_back(temp.at(i));
						}
					}
				}

				sort(mixed_boxes.begin(), mixed_boxes.end(), BoxFactory::compare_boxes_des);
				partition_map.erase(n_boxes.at(k));
				for(int j = 0; j < n_branch.size(); j++)
				{
					for (int i = 0; i < mixed_boxes.size(); i++)
					{
						partition_map[n_branch.at(j)].push_back(mixed_boxes.at(i));
					}
				}
			}
			mixed_boxes.clear();
		}

		n_boxes.clear();
		for(int i = 0; i < mixed_n_boxes.size(); i++)
		{
			n_boxes.push_back(mixed_n_boxes.at(i));
		}
		mixed_n_boxes.clear();
	}

	cout << "Resulting map:" << endl;
	for(auto it = P_result.begin(); it != P_result.end(); it++)
	{
		cout << setprecision(5) << scientific << "P(" << it->first << ") = " << it->second << " | " << width(it->second) << endl;
	}

	return P_result;
}

DInterval solution_guided(pdrh_model model, old_Box domain, DInterval init_prob)
{
	double startTime = time(NULL);

	DecisionProcedure dec_proc = DecisionProcedure(dreach_bin, dreach_options, dreal_options);
	DInterval P_lower = init_prob.leftBound();
	DInterval P_upper = init_prob.rightBound();

	vector<old_Box> mixed_boxes;
	vector<old_Box> cart_prod;
	cart_prod.push_back(domain);

	if(verbose)
	{
		cout << "|-------------------------------------------------------------------------------------|" << endl;
		cout << "|-------------------------------BRANCH AND EVALUATE-----------------------------------|" << endl;
		cout << "|-------------------------------------------------------------------------------------|" << endl;
		cout << "| Probability interval         | Precision    | Time per iteration | Total time       |" << endl;
		cout << "|-------------------------------------------------------------------------------------|" << endl;
		cout << "| [" << setprecision(16) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
	}

	//sorting initial partition
	sort(cart_prod.begin(), cart_prod.end(), BoxFactory::compare_boxes_des);

	while(true)
	{
		vector<old_Box> result;
		#pragma omp parallel
		{
			#pragma omp for schedule(dynamic)
			for(int j = 0; j < cart_prod.size(); j++)
			{
				double operationTime = time(NULL);
				old_Box box = cart_prod.at(j);
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
				result = dec_proc.evaluate_guided(rv_model, box.get_min_width() / 1000000);
				int is_borel = 0;
				if(result.at(0).get_dimension_size() == 0)
				{
					is_borel = -1;
				}
				else
				{
					if(result.at(1).get_dimension_size() == 0)
					{
						is_borel = 1;
					}
					else
					{
						// outputting solution
						for(int i = 0; i < result.size(); i++)
						{
							old_Box temp_box = result.at(i);
							vector<PartialSum> temp_vector;
							for(int k = 0; k < temp_box.get_dimension_size(); k++)
							{
								DInterval interv = temp_box.get_dimension(k).get_interval();
								temp_vector.push_back(PartialSum(temp_box.get_dimension(k).get_var(),
																 temp_box.get_dimension(k).get_fun(),
																 DInterval(interv.leftBound() - box.get_min_width() / 1000000, interv.rightBound() + box.get_min_width() / 1000000)));
							}
							result.at(i) = old_Box(temp_vector);


						}

						cout << "Solution relaxed: " << endl;
						for(int i = 0; i < result.size(); i++)
						{
							cout << i << scientific << setprecision(12) << ") " << result.at(i) << endl;
							cout << "Cut: " << endl;
							vector<old_Box> cut = BoxFactory::cut_box(box, result.at(i));
							for(int k = 0; k < cut.size(); k++)
							{
								cout << i << "." << k << scientific << setprecision(12) << ") " << cut.at(k) << endl;
							}
						}

					}
				}

				// interpreting the result
				#pragma omp critical
				{
					if(is_borel == -1)
					{
						P_upper -= box.get_value();
						if(verbose)
						{
							cout << "| [" << setprecision(16) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - operationTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
						}
					}
					if(is_borel == 1)
					{
						P_lower += box.get_value();
						if(verbose)
						{
							cout << "| [" << setprecision(16) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - operationTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
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
							//mixed_boxes.push_back(box);
							vector<old_Box> temp = BoxFactory::cut_box(box, result.at(0));
							/*
							cout << "old_Box: " << scientific << setprecision(16) <<  box << endl;
							cout << "Solution: " << scientific << setprecision(16) << result.at(0) << endl;
							cout << "Cut: " << endl;
							for(int k = 0; k < temp.size(); k++)
							{
								cout << k << scientific << setprecision(16) << ") " << temp.at(k) << endl;
							}
							*/
							cout << "delta = " << scientific << setprecision(16) << box.get_min_width() / 1000000 << endl;
							//vector<old_Box> temp = BoxFactory::branch_box(box);
							for(int k = 0; k < temp.size(); k++)
							{
								mixed_boxes.push_back(temp.at(k));
							}
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

		/*
		for(int i = 0; i < mixed_boxes_size; i++)
		{
			old_Box box = mixed_boxes.front();
			mixed_boxes.erase(mixed_boxes.begin());
			//vector<old_Box> temp = BoxFactory::cut_box(box, result[0]);
			vector<old_Box> temp = BoxFactory::branch_box(box);
			for(int j = 0; j < temp.size(); j++)
			{
				mixed_boxes.push_back(temp.at(j));
			}
		}
		 */

		/*
		if(mixed_boxes.size() < num_threads)
		{
			while (mixed_boxes.size() < num_threads)
			{
				old_Box box = mixed_boxes.front();
				mixed_boxes.erase(mixed_boxes.begin());
				vector<old_Box> temp = BoxFactory::branch_box(box);

				for(int i = 0; i < temp.size(); i++)
				{
					mixed_boxes.push_back(temp.at(i));
				}
			}
		}
		 */


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
		cout << "| [" << setprecision(16) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << epsilon << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec |" << endl;
		cout << "|-------------------------------------------------------------------------------------|" << endl;
	}

	return DInterval(P_lower.leftBound(), P_upper.rightBound());
}

DInterval evaluate_pha(pdrh_model model)
{
	vector<DInterval> P;
	DInterval P_final(0.0);
	vector<old_Box> dd_cart_prod;
	vector<old_Box> rv_cart_prod;
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
	old_Box domain;
	if(model.rvs.size() > 0)
	{
		MulRVIntegral mul_integral(model.rvs, inf_coeff, epsilon);
		rv_cart_prod = BoxFactory::calculate_cart_prod(mul_integral.get_partial_sums());
		init_prob = DInterval(0.0, 2.0 - mul_integral.get_value().leftBound());
		vector<PartialSum> partial_sums;
		for(int i = 0; i < model.rvs.size(); i++)
		{
			partial_sums.push_back(PartialSum(model.rvs.at(i).get_var(), model.rvs.at(i).get_pdf(), model.rvs.at(i).get_domain()));
		}
		domain = old_Box(partial_sums);
	}

	// case when only RVs are present
	if(dd_cart_prod.size() == 0)
	{
		if(guided)
		{
			P.push_back(solution_guided(model, domain, init_prob));
		}
		else
		{
			P.push_back(branch_and_evaluate(model, rv_cart_prod, init_prob));
		}
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
				s << "#define " << dd_cart_prod.at(i).get_var_of(j) << " " << dd_cart_prod.at(i).get_interval_of(j).leftBound();
				dd_model.defs.push_back(s.str());
				s.str("");
			}
			// case	when both RVs and DDs are present
			if (rv_cart_prod.size() > 0)
			{
				if(guided)
				{
					P.at(i) *= solution_guided(dd_model, domain, init_prob);
				}
				else
				{
					P.at(i) *= branch_and_evaluate(dd_model, rv_cart_prod, init_prob);
				}
			}
			// case when only DDs are present
			else
			{
				DecisionProcedure dec_proc(dreach_bin, dreach_options, dreal_options);
				vector<old_Box> result = dec_proc.evaluate_guided(dd_model, -1);
				// outputting solution
				int res = 0;
				if(result.at(0).get_dimension_size() == 0)
				{
					P.at(i) *= DInterval(0.0);
				}
				else
				{
					if(result.at(1).get_dimension_size() == 0)
					{
						P.at(i) *= DInterval(1.0);
					}
					else
					{
						/*
						cout << "Solution: " << endl;
						for(int i = 0; i < result.size(); i++)
						{
							cout << i << scientific << setprecision(12) << ") " << result.at(i) << endl;
						}
						P.at(i) *= DInterval(0.0, 1.0);
						*/
					}
				}
			}
			if(verbose)
			{
				cout << scientific << "P(" << dd_cart_prod.at(i) << ") = " << setprecision(16) << P.at(i) << endl;
			}
		}
	}

	// calculating final result
	for(int i = 0; i < P.size(); i++)
	{
		P_final += P.at(i);
	}

	return P_final;
}

std::map<old_Box, DInterval> evaluate_npha(pdrh_model model)
{
	std::map<old_Box, DInterval> p_dd, p_res, p_temp;
	vector<old_Box> stack_dd, stack_rv, stack_nondet;

	bool flag_rv = true;
	bool flag_nondet = true;

	if(model.rvs.empty())
	{
		model.rvs.push_back(RV("U", "dummy_rv", "1", DInterval(0, 1)));
		flag_rv = false;
	}

	if(model.dds.empty())
	{
		vector<double> arg;
		vector<double> value;
		arg.push_back(0.0);
		value.push_back(1.0);
		model.dds.push_back(DD("dummy_dd", arg, value));
	}

	if(model.params.empty())
	{
		var_type dummy_nondet;
		dummy_nondet.name = "dummy_nondet";
		dummy_nondet.range = DInterval(0,1);
		model.params.push_back(dummy_nondet);
		flag_nondet = false;
	}

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
	stack_dd = BoxFactory::calculate_cart_prod(dd_partial_sums);
	// constructing discrete probability vector
	for(int i = 0; i < stack_dd.size(); i++)
	{
		p_dd[stack_dd.at(i)] = DInterval(1.0);
		for(int j = 0; j < stack_dd.at(i).get_dimensions().size(); j++)
		{
			p_dd[stack_dd.at(i)] *= stack_dd.at(i).get_dimension(j).get_value();
		}
	}

	// obtaining Cartesian product of RVs
	MulRVIntegral mul_integral(model.rvs, inf_coeff, epsilon);
	vector<old_Box> partition_rv = BoxFactory::calculate_cart_prod(mul_integral.get_partial_sums());
	DInterval init_prob = DInterval(0.0, 2.0 - mul_integral.get_value().leftBound());
	vector<PartialSum> partial_sums;
	for(int i = 0; i < model.rvs.size(); i++)
	{
		partial_sums.push_back(PartialSum(model.rvs.at(i).get_var(), model.rvs.at(i).get_pdf(), model.rvs.at(i).get_domain()));
	}
	old_Box domain = old_Box(partial_sums);

	// obtaining domain of nondeterministic parameters
	vector<PartialSum> nondet_intervals;

	for(int i = 0; i < model.params.size(); i++)
	{
		nondet_intervals.push_back(PartialSum(model.params.at(i).name, "1", model.params.at(i).range));
	}

	stack_nondet.push_back(old_Box(nondet_intervals));

	// making all the threads busy
	if(stack_nondet.size() < num_threads)
	{
		while (stack_nondet.size() < num_threads)
		{
			old_Box box = stack_nondet.front();
			stack_nondet.erase(stack_nondet.begin());
			vector<old_Box> temp = BoxFactory::branch_box(box);
			for(int i = 0; i < temp.size(); i++)
			{
				stack_nondet.push_back(temp.at(i));
			}
		}
	}

	// partition_map
	std::map<old_Box, vector<old_Box> > partition_map;

	// initializing probability map
	for(int i = 0; i < stack_nondet.size(); i++)
	{
		p_res[stack_nondet.at(i)] = DInterval(0.0);
	}

	DecisionProcedure dec_proc = DecisionProcedure(dreach_bin, dreach_options, dreal_options);
	//omp_set_nested(1);
	//#pragma omp parallel for schedule(dynamic,1)
	for(int i = 0; i < stack_dd.size(); i++)
	{
		old_Box box_dd = stack_dd.at(i);
		pdrh_model model_dd = model;

		stringstream s;
		for (int j = 0; j < box_dd.get_dimension_size(); j++)
		{
			s << "#define " << box_dd.get_var_of(j) << " " << box_dd.get_interval_of(j).leftBound();
			model_dd.defs.push_back(s.str());
			s.str("");
		}
		// initializing partition map
		for (int j = 0; j < stack_nondet.size(); j++)
		{
			p_temp[stack_nondet.at(j)] = init_prob;
			partition_map[stack_nondet.at(j)] = partition_rv;
		}
		while(!p_temp.empty())
		{
			vector<old_Box> stack_nondet_mix;
			//#pragma omp parallel
			//{
				//#pragma omp for schedule(dynamic,1)
				for(int kk = 0; kk < stack_nondet.size(); kk++)
				{
					old_Box box_nondet = stack_nondet.at(kk);
					pdrh_model model_nondet = model_dd;
					stringstream s;
					for (int j = 0; j < box_nondet.get_dimension_size(); j++)
					{
						s << "#define _" << box_nondet.get_var_of(j) << "_a " << box_nondet.get_interval_of(j).leftBound() << endl;
						model_nondet.defs.push_back(s.str());
						s.str("");
						s << "#define _" << box_nondet.get_var_of(j) << "_b " << box_nondet.get_interval_of(j).rightBound() << endl;
						model_nondet.defs.push_back(s.str());
						s.str("");
					}
					// initializing the probability value and removing the value from the probability map
					DInterval p_value = p_temp[box_nondet];
					//#pragma omp critical
					//{
						p_temp.erase(box_nondet);
						// initializing rv stack and removing the value from the partition map
						stack_rv = partition_map[box_nondet];
						partition_map.erase(box_nondet);
						// mixed rv stack
					//}
					vector<old_Box> stack_rv_mix;
					#pragma omp parallel for schedule(dynamic,1)
					for(int k = 0; k < stack_rv.size(); k++)
					{
						old_Box box_rv = stack_rv.at(k);
						pdrh_model model_rv = model_nondet;

						if(flag_rv)
						{
							stringstream s;
							for (int j = 0; j < box_rv.get_dimension_size(); j++)
							{
								s << "#define _" << box_rv.get_var_of(j) << "_a " <<
								box_rv.get_interval_of(j).leftBound() << endl;
								model_rv.defs.push_back(s.str());
								s.str("");
								s << "#define _" << box_rv.get_var_of(j) << "_b " <<
								box_rv.get_interval_of(j).rightBound() << endl;
								model_rv.defs.push_back(s.str());
								s.str("");
								var_type var;
								var.name = model_rv.rvs.at(j).get_var();
								double radius = 100 * (model_rv.rvs.at(j).get_domain().rightBound() -
													   model_rv.rvs.at(j).get_domain().leftBound());
								var.range = DInterval(model_rv.rvs.at(j).get_domain().leftBound() - radius,
													  model_rv.rvs.at(j).get_domain().rightBound() + radius);
								model_rv.vars.push_back(var);
							}
						}
						//cout << "Thread num = " << omp_get_thread_num()	<< endl;
						// evaluating the boxes
						int eval = dec_proc.evaluate(model_rv, box_rv.get_min_width() / 1000);
						// interpreting the result
						#pragma omp critical
						{
							switch (eval)
							{
								case -1:
									p_value = DInterval(p_value.leftBound(), p_value.rightBound() - box_rv.get_value().leftBound());
									//cout << setprecision(8) << scientific << p_value << " | " << width(p_value) << endl;
									break;
								case 1:
									p_value = DInterval(p_value.leftBound() + box_rv.get_value().leftBound(), p_value.rightBound());
									//cout << setprecision(8) << scientific << p_value << " | " << width(p_value) << endl;
									break;
								case 0:
									//cout << "For RV box " << box_rv << " is undecidable" << endl;
									// branching boxes here
									if(flag_rv)
									{
										vector <old_Box> branch_rv = BoxFactory::branch_box(box_rv);
										for (int j = 0; j < branch_rv.size(); j++)
										{
											stack_rv_mix.push_back(branch_rv.at(j));
										}
									}
									else
									{
										stack_rv_mix.push_back(box_rv);
									}
									break;
							}
							cout << setprecision(8) << scientific << p_value << " | " << width(p_value) << endl;
						}
					}
					// checking the width of probability interval and the maximum dimension of nondeterministic box
					//cout << setprecision(8) << scientific << p_value << " | " << width(p_value) << endl;
					#pragma omp critical
					{
						if((width(p_value) <= epsilon) || (box_nondet.get_max_width() <= max_nondet))
						{
							p_res[box_nondet] += p_value * box_dd.get_value();
						}
						else
						{
							if(flag_nondet)
							{
								vector <old_Box> branch_nondet = BoxFactory::branch_box(box_nondet);
								// sorting the branched boxes
								sort(stack_rv_mix.begin(), stack_rv_mix.end(), BoxFactory::compare_boxes_des);
								DInterval p_temp_value = p_res[box_nondet];
								p_res.erase(box_nondet);
								for (int j = 0; j < branch_nondet.size(); j++)
								{
									p_temp[branch_nondet.at(j)] = p_value;
									// updating the resulting probability map
									p_res[branch_nondet.at(j)] = p_temp_value;
									partition_map[branch_nondet.at(j)] = stack_rv_mix;
								}
							}
							else
							{
								p_temp[box_nondet] = p_value;
								partition_map[box_nondet] = stack_rv_mix;
							}
						}
						stack_rv_mix.clear();
					}
				}
			//}
			cout << "intermediate p_res " << box_dd << endl;
			for(auto it = p_res.begin(); it != p_res.end(); it++)
			{
				cout << setprecision(5) << scientific << "P(" << it->first << ") = " << p_res[it->first] << " | " << width(p_res[it->first]) << endl;
			}
			stack_nondet.clear();
			// setting nondeterministic boxes
			for(auto it = p_temp.begin(); it != p_temp.end(); it++)
			{
				stack_nondet.push_back(it->first);
			}
		}
		for(auto it = p_res.begin(); it != p_res.end(); it++)
		{
			stack_nondet.push_back(it->first);
		}
	}

	return p_res;
}

vector<old_Box> prepartition(vector<old_Box> boxes, std::map<string, double> precision)
{
	vector<old_Box> tmp_list;
	for(long int i = 0; i < boxes.size(); i++)
	{
		tmp_list.push_back(boxes.at(i));
	}
	boxes.clear();

	while(tmp_list.size() > 0)
	{
		old_Box tmp_box = tmp_list.front();
		tmp_list.erase(tmp_list.begin());
		if (tmp_box.get_max_width() > 0)
		{
			vector<old_Box> tmp_vector = BoxFactory::branch_box(tmp_box, precision);
			//vector<old_Box> tmp_vector = BoxFactory::branch_box(tmp_box, epsilon);
			//vector<old_Box> tmp_vector = BoxFactory::branch_box(tmp_box);
			if(tmp_vector.size() == 1)
			{
				boxes.push_back(tmp_box);
			}
			else
			{
				for(long int i = 0; i < tmp_vector.size(); i++)
				{
					tmp_list.push_back(tmp_vector.at(i));
				}
			}
		}
		else
		{
			boxes.push_back(tmp_box);
		}
	}

	return boxes;
}

void synthesize(pdrh_model model, std::map<string, vector<DInterval>> csv)
{
	pugi::xml_node root_node;
	std::stringstream s;
	s << filename << "." << time(NULL) << ".xml";
	string xml_filename = s.str();
	if(xml_output_flag)
	{
		root_node.set_name("data");
		root_node.append_attribute("progress");
		root_node.attribute("progress").set_value(100);

		xml_output.append_child("data").append_attribute("progress").set_value(100);
	}

	// parameter domain
	vector<PartialSum> dimensions;
	cout << "Parameters to synthesise:" << endl;

	for(auto it = model.param_syn.begin(); it != model.param_syn.end(); it++)
	{
		for(int i = 0; i < model.params.size(); i++)
		{
			if(strcmp(it->first.c_str(), model.params.at(i).name.c_str()) == 0)
			{
				dimensions.push_back(PartialSum(model.params.at(i).name, "", model.params.at(i).range, -1));
				cout << i << ") " << model.params.at(i).name << " with precision : " << model.param_syn[model.params.at(i).name] << endl;
			}
		}
	}

	/*
	for(int i = 0; i < model.params.size(); i++)
	{
		cout << i << ") " << model.params.at(i).name << endl;
		dimensions.push_back(PartialSum(model.params.at(i).name, "", model.params.at(i).range, -1));
	}
	*/
	old_Box domain(dimensions);

	cout << "Parameter domain: " << domain << endl;

	// getting number of time points
	int series_size = csv.begin()->second.size();

	cout << "Series size: " << series_size << " time points" << endl;

	// initializing the stack
	vector<old_Box> boxes;
	boxes.push_back(domain);
	if(prepartition_flag)
	{
		boxes = prepartition(boxes, model.param_syn);
	}

	cout << "Domain: " << domain << endl;
	CSVParser::display(csv, " ");

	// initializing stacks

	vector<old_Box> sat_boxes, unsat_boxes, undec_boxes;

	int mode_disp, step_disp;
	double time_disp;

	int prev_mode = model.init.mode;

	for(int i = 0; i < series_size; i++)
	{
		mode_disp = (int) csv["Mode"].at(i).leftBound();
		step_disp = (int) csv["Step"].at(i).leftBound();
		time_disp = (double) csv["Time"].at(i).leftBound();

		for(int j = 0; j < model.vars.size(); j++)
		{
			if(strcmp(model.vars.at(j).name.c_str(),"tau") == 0)
			{
				//cout << model.vars.at(j).name << " : " << model.vars.at(j).range << " time disp " << time_disp << endl;
				model.vars.at(j).range = DInterval(0, time_disp);
			}
			if(strcmp(model.vars.at(j).name.c_str(),"time") == 0)
			{
				//cout << model.vars.at(j).name << " : " << model.vars.at(j).range << " time disp " << time_disp << endl;
				model.vars.at(j).range = DInterval(0, time_disp);
			}
		}

		if(mode_disp != prev_mode)
		{
			for(int j = 0; j < model.modes.size(); j++)
			{
				if(model.modes.at(j).id == prev_mode)
				{
					for(int k = 0; k < model.modes.at(j).jumps.size(); k++)
					{
						stringstream tmp_stream;
						tmp_stream << "(and " << model.modes.at(j).jumps.at(k).guard << "(tau>=" << csv["Time"].at(i-1).leftBound() << ")(tau<=" << csv["Time"].at(i).leftBound() <<"))";
						model.modes.at(j).jumps.at(k).guard = tmp_stream.str();
						cout << "Changing mode from " << prev_mode << " to " << mode_disp << " with guard " << model.modes.at(j).jumps.at(k).guard << endl;
					}
				}
			}
			prev_mode = mode_disp;
		}

		model.modes[csv["Mode"].at(i).leftBound()];

		model.goal.mode = csv["Mode"].at(i).leftBound();
		model.goal_c.mode = csv["Mode"].at(i).leftBound();
		stringstream s;
		s << "(and ";
		for(auto it = csv.begin(); it != csv.end(); it++)
		{
			if(!((strcmp(it->first.c_str(), "Time") == 0) ||
					(strcmp(it->first.c_str(), "Mode") == 0) ||
					(strcmp(it->first.c_str(), "Step") == 0)))
			{
				double left_bound = it->second.at(i).leftBound();
				if(!std::isnan(left_bound))
				{
					s << "(" << it->first << " >= " << it->second.at(i).leftBound() << ")";
					s << "(" << it->first << " <= " << it->second.at(i).rightBound() << ")";
				}
				//else
				//{
				//	cout << it->second.at(i).leftBound() << endl;
				//}
			}
		}
		s << ")";
		stringstream tmp;
		tmp << "(and (tau = " << csv["Time"].at(i).leftBound() << ") " << s.str() << ")";
		model.goal.formula = tmp.str();
		tmp.str("");
		tmp << "(and (tau = " << csv["Time"].at(i).leftBound() << ") (not " << s.str() << "))";
		model.goal_c.formula = tmp.str();
		tmp.str("");
		tmp << "-l " << csv["Step"].at(i).leftBound() << " -k " << csv["Step"].at(i).leftBound() << " -z";
		dreach_options = tmp.str();

		while(true)
		{
			vector<old_Box> branched_boxes;
			#pragma omp parallel for
			for(int j = 0; j < boxes.size(); j++)
			{
				pdrh_model tmp_model = model;
				old_Box box = boxes.at(j);

				for(int k = 0; k < box.get_dimension_size(); k++)
				{
					for(int l = 0; l < tmp_model.vars.size(); l++)
					{
						stringstream s;
						if(strcmp(box.get_var_of(k).c_str(), tmp_model.vars.at(l).name.c_str()) == 0)
						{
							s << "#define _" << box.get_var_of(k) << "_a " << box.get_interval_of(k).leftBound();
							tmp_model.defs.push_back(s.str());
							s.str("");
							s << "#define _" << box.get_var_of(k) << "_b " << box.get_interval_of(k).rightBound();
							tmp_model.defs.push_back(s.str());
							s.str("");
						}
						if(strcmp(domain.get_var_of(k).c_str(), tmp_model.vars.at(l).name.c_str()) == 0)
						{
							//double radius = 10 * width(domain.get_interval_of(k));
							double radius = 0;
							tmp_model.vars.at(l).range = DInterval(tmp_model.vars.at(l).range.leftBound() - radius, model.vars.at(l).range.rightBound() + radius);
						}
					}
				}

				int eval_res = evaluate_ha(tmp_model);

				#pragma omp critical
				{
					switch (eval_res)
					{
						case -1:
							unsat_boxes.push_back(box);
							//cout << "unsat" << endl;
							break;
						case 1:
							sat_boxes.push_back(box);
							//cout << "sat" << endl;
							break;
						case 0:
							vector<old_Box> tmp_vector = BoxFactory::branch_box(box, model.param_syn);
							//cout << "undec" << endl;
							if(tmp_vector.size() == 1)
							{
								undec_boxes.push_back(box);
							}
							else
							{
								for (int j = 0; j < tmp_vector.size(); j++)
								{
									branched_boxes.push_back(tmp_vector.at(j));
								}
							}
							break;
					}
				}
			}

			boxes.clear();

			if(branched_boxes.size() == 0) break;

			for(int j = 0; j < branched_boxes.size(); j++)
			{
				boxes.push_back(branched_boxes.at(j));
			}

		}

		// saving SAT boxes
		/*
		for(int j = 0; j < sat_boxes.size(); j++)
		{
			boxes.push_back(sat_boxes.at(j));
		}
		 */

		if(merge_flag)
		{
			sat_boxes = BoxFactory::merge_boxes(sat_boxes);
			unsat_boxes = BoxFactory::merge_boxes(unsat_boxes);
			undec_boxes = BoxFactory::merge_boxes(undec_boxes);
		}

		// finding node by the attribute name and value
		if(xml_output_flag)
		{
			stringstream s;
			s << time_disp;
			pugi::xml_node point = xml_output.child("data").find_child_by_attribute("point", "time", s.str().c_str());
			// if node already exists we remove it
			if (!point.empty())
			{
				xml_output.child("data").remove_child(point);
			}
			point = xml_output.child("data").append_child("point");
			point.append_attribute("time").set_value(time_disp);
			// output sat boxes
			for(int k = 0; k < sat_boxes.size(); k++)
			{
				old_Box box = sat_boxes.at(k);
				pugi::xml_node box_node = point.append_child("box");
				box_node.append_attribute("type").set_value("sat");
				for(int j = 0; j < box.get_dimension_size(); j++)
				{
					pugi::xml_node interval_node = box_node.append_child("interval");
					interval_node.append_attribute("var").set_value(box.get_dimension(j).get_var().c_str());
					interval_node.append_attribute("left").set_value(box.get_dimension(j).get_interval().leftBound());
					interval_node.append_attribute("right").set_value(box.get_dimension(j).get_interval().rightBound());
				}
			}

			// output unsat boxes
			for(int k = 0; k < unsat_boxes.size(); k++)
			{
				old_Box box = unsat_boxes.at(k);
				pugi::xml_node box_node = point.append_child("box");
				box_node.append_attribute("type").set_value("unsat");
				for(int j = 0; j < box.get_dimension_size(); j++)
				{
					pugi::xml_node interval_node = box_node.append_child("interval");
					interval_node.append_attribute("var").set_value(box.get_dimension(j).get_var().c_str());
					interval_node.append_attribute("left").set_value(box.get_dimension(j).get_interval().leftBound());
					interval_node.append_attribute("right").set_value(box.get_dimension(j).get_interval().rightBound());
				}
			}

			// output undec boxes
			for(int k = 0; k < undec_boxes.size(); k++)
			{
				old_Box box = undec_boxes.at(k);
				pugi::xml_node box_node = point.append_child("box");
				box_node.append_attribute("type").set_value("undec");
				for(int j = 0; j < box.get_dimension_size(); j++)
				{
					pugi::xml_node interval_node = box_node.append_child("interval");
					interval_node.append_attribute("var").set_value(box.get_dimension(j).get_var().c_str());
					interval_node.append_attribute("left").set_value(box.get_dimension(j).get_interval().leftBound());
					interval_node.append_attribute("right").set_value(box.get_dimension(j).get_interval().rightBound());
				}
			}

			xml_output.save_file(xml_filename.c_str());
		}

		cout << "====================" << endl;
		cout << "Step : " << step_disp << " Mode : " << mode_disp << " Time : " << time_disp << endl;
		cout << "SAT boxes:" << endl;
		for(int j = 0; j < sat_boxes.size(); j++)
		{
			cout << j << ") " << sat_boxes.at(j) << endl;
			boxes.push_back(sat_boxes.at(j));
		}
		cout << "UNDEC boxes:" << endl;
		for(int j = 0; j < undec_boxes.size(); j++)
		{
			cout << j << ") " << undec_boxes.at(j) << endl;
		}
		cout << "UNSAT boxes:" << endl;
		for(int j = 0; j < unsat_boxes.size(); j++)
		{
			cout << j << ") " << unsat_boxes.at(j) << endl;
		}

		if(sat_boxes.size() == 0)
		{
			cout << "Problem is UNSAT" << endl;
			break;
		}

		if(prepartition_flag)
		{
			boxes = prepartition(boxes, model.param_syn);
		}

		sat_boxes.clear();
		unsat_boxes.clear();
		undec_boxes.clear();
		cout << "====================" << endl;
	}
}

void print_help()
{
	cout << endl;
	cout << "Help message:" << endl;
	cout << endl;
	cout << "	Run ./ProbReach <options> <file.pdrh/file.drh> <solver-options>" << endl;
	cout << endl;
	cout << "options:" << endl;
	cout << "	-e <double> - length of probability interval or maximum length of the box (default 0.001)" << endl;
	cout << "	-l/--solver </path/to/solver> - full path to the solver (default dReal)" << endl;
	cout << "	-t <int> - number of CPU cores (default " << max_num_threads << ") (max " << max_num_threads << ")" << endl;
	cout << "	-h/--help - help message" << endl;
	cout << "	--version - version of the tool" << endl;
	cout << "	--verbose - output computation details" << endl;
	//cout << "	--visualize <char*> - visualize output for specified continuous random parameter" << endl;
	//cout << "	--dreach - delimits dReach options (e.g. rechability depth)" << endl;
	//cout << "	--dreal - delimits dReal options (e.g. precision, ode step)" << endl;
	cout << endl;
}

//void print_version()
//{
//	cout << "ProbReach " << PROBREACH_VERSION << endl;
//}

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
	// parsing options
	int opt_end = argc;
	stringstream s;
	cmatch matches;
	//parsing ProbReach options
	for(int i = 1; i < argc; i++)
	{
		//extracting a file name
		if(regex_match(argv[i], matches, regex("(.*/)*(.*).pdrh")) ||
		   regex_match(argv[i], matches, regex("(.*/)*(.*).drh")))
		{
			filename = matches[1].str() + matches[2].str();
			opt_end = i;
			break;
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
			// max_nondet
		else if(strcmp(argv[i], "--max_nondet") == 0)
		{
			i++;
			istringstream is(argv[i]);
			is >> max_nondet;
			if(max_nondet <= 0)
			{
				cerr << "-e should be positive" << endl;
				exit(EXIT_FAILURE);
			}
		}
			// noise
			/*
            else if(strcmp(argv[i], "--noise") == 0)
            {
                i++;
                istringstream is(argv[i]);
                is >> series_noise;
                if(series_noise <= 0)
                {
                    cerr << "--noise should be positive" << endl;
                    exit(EXIT_FAILURE);
                }
            }
            */
			// time series filename
		else if(strcmp(argv[i], "--series") == 0)
		{
			i++;
			series_filename = argv[i];
			istringstream is(argv[i]);
		}
			//dReal binary
		else if((strcmp(argv[i], "-l") == 0) || (strcmp(argv[i], "--solver")))
		{
			i++;
			ostringstream os;
			os << argv[i];
			dreach_bin = os.str();
		}
			//verbose
		else if(strcmp(argv[i], "--verbose") == 0)
		{
			verbose = true;
		}
			//merge flag
		else if(strcmp(argv[i], "--merge-boxes") == 0)
		{
			merge_flag = true;
		}
			//xml_output
		else if(strcmp(argv[i], "--xml-output") == 0)
		{
			xml_output_flag = true;
		}
			//solution-guided
		else if(strcmp(argv[i], "--guided") == 0)
		{
			guided = true;
		}
			//prepartition flag
		else if(strcmp(argv[i], "--partition") == 0)
		{
			prepartition_flag = true;
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
	// getting solver options
	for(int i = opt_end + 1; i < argc; i++)
	{
		stringstream s;
		s << argv[i] << " ";
		solver_opt = s.str();
	}
	// case if filename is not specified
	if(strcmp(filename.c_str(), "") == 0)
	{
		cerr << "model file is not specified" << endl;
		print_help();
		exit(EXIT_FAILURE);
	}
	// default solver binary is dReal
	if(strcmp(solver_bin.c_str(), "") == 0)
	{
		solver_bin = "dReal";
	}
}

int main(int argc, char* argv[])
{


	/*
	// setting max number of threads by default
	#ifdef _OPENMP
		max_num_threads = omp_get_max_threads();
		num_threads = max_num_threads;
		omp_set_num_threads(num_threads);
	#endif

	cout.precision(16);

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

	cout << "Parameters" << endl;
	for(int i = 0; i < model.params.size(); i++)
	{
		cout << i << ") " << model.params.at(i).name << " " << model.params.at(i).range << endl;
	}

	std::map<old_Box, DInterval> p_map;
	switch (model.model_type)
	{
		case 1:
			switch (evaluate_ha(model))
			{
				case -1:
					cout << "unsat" << endl;
					break;
				case 0:
					cout << "undec" << endl;
					break;
				case 1:
					cout << "sat" << endl;
					break;
			}
			break;
		case 2:
			cout << setprecision(12) << scientific <<  evaluate_pha(model) << endl;
			break;
		case 3:
			p_map = evaluate_npha(model);
			cout << "==============================" << endl;
			cout << "Probability map:" << endl;
			for (auto it = p_map.begin(); it != p_map.end(); it++)
			{
				cout << setprecision(5) << scientific << "P(" << it->first << ") = " << it->second << " | " << width(it->second) << endl;
			}
			//cout << setprecision(12) << scientific <<  evaluate_npha(model) << endl;
			//cout << "OLD" << endl;
			//cout << setprecision(12) << scientific <<  evaluate_pha(model) << endl;
			break;
		case 4:
			//std::map<string, vector<DInterval>> csv =  CSVParser::parse(series_filename, series_noise);
			//CSVParser::display(csv, "\t\t");
			std::map<string, vector<DInterval>> csv =  CSVParser::parse(series_filename);
			synthesize(model, csv);
			break;
	}
	*/

	// setting max number of threads by default
	#ifdef _OPENMP
		max_num_threads = omp_get_max_threads();
		num_threads = max_num_threads;
		omp_set_num_threads(num_threads);
	#endif

	cout.precision(16);

	// parse command line
	parse_pdrh_config(argc, argv);

	std::cout << "Parsing " << global_config.model_filename;
	// open a file handle to a particular file:
	FILE *pdrhfile = fopen(global_config.model_filename.c_str(), "r");
	// make sure it's valid:
	if (!pdrhfile)
	{
		std::cout << "Couldn't open " << global_config.model_filename << std::endl;
		return -1;
	}
	// preprocessing the file
	std::stringstream s, pdrhnameprep;
	pdrhnameprep << global_config.model_filename << ".preprocessed";
	s << "cpp -w -P " << global_config.model_filename << " > " << pdrhnameprep.str().c_str();
	system(s.str().c_str());
	// parsing the preprocessed file
	FILE *pdrhfileprep = fopen(pdrhnameprep.str().c_str(), "r");
	// make sure it's valid:
	if (!pdrhfileprep)
	{
		std::cout << "Couldn't open " << pdrhnameprep << std::endl;
		return -1;
	}
	// set lex to read from it instead of defaulting to STDIN:
	yyin = pdrhfileprep;
	// parse through the input until there is no more:
	do
	{
		yyparse();
	}
	while (!feof(yyin));
	std::remove(pdrhnameprep.str().c_str());
	std::cout << " --- OK" << std::endl;
	std::cout << "dd map:" << std::endl;
	for(auto it = pdrh::dd_map.cbegin(); it != pdrh::dd_map.cend(); it++)
	{
		std::cout << it->first << std::endl;
		for(auto it2 = it->second.cbegin(); it2 != it->second.cend(); it2++)
		{
			std::cout << it2->first << " : " << it2->second << std::endl;
		}
	}
	// retrieving all possible paths of length [min, max]
	std::vector<std::vector<pdrh::mode*>> paths;
	for(int i = global_config.reach_depth_min; i <= global_config.reach_depth_max; i++)
	{
		std::vector<std::vector<pdrh::mode*>> tmp_paths = pdrh::get_all_paths(i);
		for(int j = 0; j < tmp_paths.size(); j++)
		{
			paths.push_back(tmp_paths.at(j));
		}
	}
	// verifying the first formula
	int path_index = 0;
	// getting dd_boxes
	std::map<std::string, std::vector<capd::interval>> m;
	for(auto it = pdrh::dd_map.cbegin(); it != pdrh::dd_map.cend(); it++)
	{
		std::vector<capd::interval> args;
		for(auto it2 = it->second.cbegin(); it2 != it->second.cend(); it2++)
		{
			args.push_back(it2->first);
		}
		m.insert(make_pair(it->first, args));
	}
	std::vector<box> boxes = box_factory::cartesian_product(m);
	std::vector<dd_box> dd_boxes(boxes.cbegin(), boxes.cend());

	for(std::vector<pdrh::mode*> path : paths)
	{
		std::stringstream p_stream;
		for(pdrh::mode* m : path)
		{
			p_stream << m->id << " ";
		}
		for(dd_box b : dd_boxes)
		{
			//rv_box
			std::cout << "Evaluating dd box: " << b << std::endl;
			// removing trailing whitespace
			std::cout << "Evaluating path: " << p_stream.str().substr(0, p_stream.str().find_last_of(" ")) << std::endl;
			int res = decision_procedure::evaluate(path, NULL, &b, NULL);
			if(res == decision_procedure::SAT)
			{
				std::cout << "Result: " << capd::interval(1) * measure::p_measure(b) << std::endl;
			}
			else if(res == decision_procedure::UNSAT)
			{
				std::cout << "Result: " << capd::interval(0) * measure::p_measure(b) << std::endl;
			}
			else if(res == decision_procedure::UNDET)
			{
				std::cout << "Result: " << capd::interval(0, 1) * measure::p_measure(b) << std::endl;
			}
		}
		path_index++;
	}
	// ADD MODEL TYPE CHECK
	return EXIT_SUCCESS;
}






