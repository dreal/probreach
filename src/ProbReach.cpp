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
//#include "nRV.h"
#include "DecisionProcedure.h"
#include "BoxFactory.h"
#include "FileParser.h"

using namespace std;
using namespace capd;

double delta = 1e-03;
double epsilon = 1e-03;
double inf_coeff = 1e-01;
int depth = 0;
string filename;
string dreach_bin = "dReach";

ostream& operator<<(ostream& strm, Box& box)
{
	for(int i = 0; i < box.get_dimension_size() - 1; i++)
	{
		strm << box.get_interval_of(i) << "x";
	}
	strm << box.get_interval_of(box.get_dimension_size() - 1);
	
	return strm;
}

DInterval branch_and_evaluate(pdrh_model model, vector<Box> cart_prod, option_type opt, DInterval init_prob, Box dd_box)
{

	double startTime = time(NULL);

	DecisionProcedure dec_proc = DecisionProcedure(model, opt, dreach_bin);
	DInterval P_lower = init_prob.leftBound();
	DInterval P_upper = init_prob.rightBound();
	//DInterval P_upper(2.0 - mul_rv_integral.get_value().leftBound());

    //cout << getpid() << endl;
    vector<Box> mixed_boxes;

    int num_threads = 1;
	
	#ifdef _OPENMP
    	num_threads = omp_get_max_threads() - 8;
    	omp_set_num_threads(num_threads);
 	#endif
	
    cout << "|-------------------------------------------------------------------------------------|" << endl;
    cout << "|-------------------------------BRANCH AND EVALUATE-----------------------------------|" << endl;
    cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| Probability interval         | Precision    | Time per iteration | Total time       |" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
	//while(P_upper.rightBound() - P_lower.leftBound() > epsilon)
	while(true)
	{
		#pragma omp parallel
		{
			#pragma omp for schedule(dynamic)
			for(int i = 0; i < cart_prod.size(); i++)
			{
				double operationTime = time(NULL);
				Box box = cart_prod.at(i);
				//cout << "Current box : " << setprecision(12) << box << endl;
				int is_borel = dec_proc.evaluate(dd_box, box);
				
				#pragma omp critical
				{				
					if(is_borel == -1)
					{
						//cout << box << setprecision(12) << " is not in B" << endl;
						P_upper -= box.get_value();
						//cout << "Box: " << box << " is not in B" << endl;
						cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - operationTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
					}
					if(is_borel == 1)
					{
						//cout << box << setprecision(12) << " is in B" << endl;
						P_lower += box.get_value();
						//cout << "Box: " << box << " is in B" << endl;
						cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - operationTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
					}
					if(is_borel == 0)
					{
						//cout << box << setprecision(12) << " is a mixed box" << endl;
						//cout << "Box: " << setprecision(12) << box << " is mixed" << endl;
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
						//cout << "Size " << mixed_boxes.size() << endl;
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
	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| Probability interval         | Precision    | Required precision | Total time       |" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << epsilon << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec |" << endl;
	cout << "|-------------------------------------------------------------------------------------|" << endl;
	return DInterval(P_lower.leftBound(), P_upper.rightBound());
}


void print_help()
{
	cout << "Help message is printed out here" << endl;
}

void parce_cmd(int argc, char* argv[])
{
	if(argc < 2)
	{
		print_help();
		exit(EXIT_FAILURE);
	} 
	else 
	{
		filename = argv[argc - 1];
		for(int i = 1; i < argc - 1; i++)
		{
			if(strcmp(argv[i], "-e") == 0)
			{
				istringstream is(argv[i + 1]);
				is >> epsilon;
				if(epsilon <= 0)
				{
					cerr << "-e should be positive" << endl;
					exit(EXIT_FAILURE);
				}
			}
			if(strcmp(argv[i], "-d") == 0)
			{
				istringstream is(argv[i + 1]);
				is >> delta;
				if(delta <= 0)
				{
					cerr << "-d should be positive" << endl;
					exit(EXIT_FAILURE);
				}
			}
			if(strcmp(argv[i], "-k") == 0)
			{
				istringstream is(argv[i + 1]);
				is >> depth;
				if(depth < 0)
				{
					cerr << "-k should be non-negative" << endl;
					exit(EXIT_FAILURE);
				}
			}
			if(strcmp(argv[i], "-l") == 0)
			{
				ostringstream os;
				os << argv[i + 1] << "dReach";
				dreach_bin = os.str();
			}
		}
	}
}

int main(int argc, char* argv[])
{
	parce_cmd(argc, argv);
	cout << "Input arguments:" << endl;
	cout << "delta = " << delta << endl;
	cout << "epsilon = " << epsilon << endl;
	cout << "depth = " << depth << endl;
	cout << "filename = " << filename << endl;
	cout << "dReach version = " << dreach_bin << endl;

	FileParser file_parser(filename);

	pdrh_model model = file_parser.get_model();

	vector<DInterval> P;
	DInterval P_final;

	vector<Box> dd_cart_prod;
	vector<Box> rv_cart_prod;

	if(model.dds.size() > 0)
	{
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

		for(int i = 0; i < dd_cart_prod.size(); i++)
		{
			DInterval temp_P = DInterval(1.0, 1.0);
			pdrh_model temp_model = model;
			for(int j = 0; j < dd_cart_prod.at(i).get_dimensions().size(); j++)
			{
				temp_P *= dd_cart_prod.at(i).get_dimension(j).get_value();
			}
			P.push_back(temp_P);
		}
	}
	else
	{
		P.push_back(DInterval(1.0));
	}

	DInterval init_prob;
	if(model.rvs.size() > 0)
	{
		MulRVIntegral mul_integral(model.rvs, inf_coeff, epsilon);
		rv_cart_prod = BoxFactory::calculate_cart_prod(mul_integral.get_partial_sums());
		init_prob = DInterval(0.0, 2.0 - mul_integral.get_value().leftBound());
	}

	option_type opt;
	opt.delta = delta;
	opt.depth = depth;

	//HA
	if(model.model_type == 1)
	{
		DecisionProcedure dec_proc(model, opt, dreach_bin);
		Box dd_box = Box();
		Box rv_box = Box();
		int res = dec_proc.evaluate(dd_box, rv_box);
		if(res == 1)
		{
			cout << "sat" << endl;
		}
		if(res == -1)
		{
			cout << "unsat" << endl;
		}
		if(res == 0)
		{
			cout << "undec" << endl;
		}	
	}
	//PHA or NPHA
	else
	{
		cout << "Model type = " << model.model_type << endl;
		if(dd_cart_prod.size() == 0)
		{
			Box dd_box = Box();
			P.at(0) *= branch_and_evaluate(model, rv_cart_prod, opt, init_prob, dd_box);
		}
		else
		{
			for(int i = 0; i < dd_cart_prod.size(); i++)
			{
				P.at(i) *= branch_and_evaluate(model, rv_cart_prod, opt, init_prob, dd_cart_prod.at(i));
			}
		}
	}

	cout << "Probability vector:" << endl;
	for(int i = 0; i < P.size(); i++)
	{
		cout << setprecision(16) << "P(" << i << ")= " << P.at(i) << endl; 
	}

	for(int i = 0; i < P.size(); i++)
	{
		P_final += P.at(i);
	}
	cout << "P_final = " << setprecision(16) << P_final << endl;
	
	return EXIT_SUCCESS;
}






