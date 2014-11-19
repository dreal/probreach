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

	double startTime = time(NULL);

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

    cout << "|-------------------------------------------------------------------------------------|" << endl;
    cout << "|-------------------------------BRANCH AND EVALUATE-----------------------------------|" << endl;
    cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| Probability interval         | Precision    | Time per iteration | Total time       |" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
	while(P_upper.rightBound() - P_lower.leftBound() > atof(settings["precision"].c_str()))
	{
		#pragma omp parallel
		{
			#pragma omp for schedule(dynamic)
			for(int i = 0; i < cart_prod.size(); i++)
			{
				double operationTime = time(NULL);
				Box box = cart_prod.at(i);
				int is_borel = dec_proc.evaluate(box);
				
				#pragma omp critical
				{				
					if(is_borel == -1)
					{
						//cout << box << setprecision(12) << " is not in B and P in [" << P_lower.leftBound() << "," << P_upper.rightBound() << "]" << endl;
						P_upper -= box.get_value();
						cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - operationTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
					}
					if(is_borel == 1)
					{
						//cout << box << setprecision(12) << " is in B and P in [" << P_lower.leftBound() << "," << P_upper.rightBound() << "]" << endl;
						P_lower += box.get_value();
						cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - operationTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
					}
					if(is_borel == 0)
					{
						//cout << box << setprecision(12) << " is a mixed box" << endl;
						mixed_boxes.push_back(box);
						//cout << "Size " << mixed_boxes.size() << endl;
					}
				}
			}
		}

		cart_prod.clear();

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
   	cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << settings["precision"].c_str() << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec |" << endl;
	cout << "|-------------------------------------------------------------------------------------|" << endl;
}

void evaluate_and_branch(char* argv[])
{

	double startTime = time(NULL);

	FileParser file_parser(argv[1]);
	std::map<string, string> settings = file_parser.get_settings();
	vector<RV*> rv = file_parser.get_rv();
	vector<string> temp = file_parser.get_temp();
	vector<string> temp_inv = file_parser.get_temp_inv();

	MulRVIntegral mul_rv_integral = MulRVIntegral(rv, 0.1, atof(settings["precision"].c_str()));
	vector<Box> cart_prod = BoxFactory::calculate_cart_prod(mul_rv_integral.get_partial_sums());
	std::map<string, double> options = std::map<string, double>();
	DecisionProcedure dec_proc = DecisionProcedure(temp, temp_inv, rv, settings);
	
	int num_threads = 1;

    #ifdef _OPENMP
    	num_threads = omp_get_max_threads() - 8;
    	omp_set_num_threads(num_threads);
 	#endif

	vector<PartialSum> partial_sums;
	for(int i = 0; i < rv.size(); i++)
	{
		PartialSum par_sum = PartialSum(rv.at(i)->get_var(), rv.at(i)->get_pdf(), rv.at(i)->get_domain());
		partial_sums.push_back(par_sum);
	}
	Box main_box(partial_sums);

	vector<Box> boxes;
	boxes.push_back(main_box);

	//making all the cores busy
	/*
	if(boxes.size() < num_threads)
	{
		while (boxes.size() < num_threads)
    	{
    		Box box = boxes.front();
    		boxes.erase(boxes.begin());
    		vector<Box> temp = BoxFactory::branch_box(box);
    		for(int i = 0; i < temp.size(); i++)
			{
				boxes.push_back(temp.at(i));
			}
    	}
	}
	*/

	vector<Box> mixed_boxes;

	DInterval P_lower(0.0);
	DInterval P_upper(2.0 - mul_rv_integral.get_value().leftBound());

	cout << getpid() << endl;
    cout << "|-------------------------------------------------------------------------------------|" << endl;
    cout << "|-------------------------------EVALUATE AND BRANCH-----------------------------------|" << endl;
    cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| Probability interval         | Precision    | Time per iteration | Total time       |" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
	
    while(P_upper.rightBound() - P_lower.leftBound() > atof(settings["precision"].c_str()))
	{
		#pragma omp parallel
		{
			#pragma omp for schedule(dynamic)
			for(int i = 0; i < boxes.size(); i++)
			{
				double operationTime = time(NULL);
				int is_borel = dec_proc.evaluate(boxes.at(i));
				
				#pragma omp critical
				{		
					if(is_borel == -1)
					{
						boxes.at(i).set_value(mul_rv_integral.calculate_box(boxes.at(i)));
						P_upper -= boxes.at(i).get_value();
						cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - operationTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
					}
					if(is_borel == 1)
					{
						boxes.at(i).set_value(mul_rv_integral.calculate_box(boxes.at(i)));
						P_lower += boxes.at(i).get_value();
						cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - operationTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
					}
					if(is_borel == 0)
					{
						vector<Box> temp = BoxFactory::branch_box(boxes.at(i));
						//cout << setprecision(12) << boxes.at(i) << " IS MIXED OF " << mixed_boxes.size() << endl;
						for(int j = 0; j < temp.size(); j++)
						{
							Box temp_box(temp.at(j));
							temp_box.set_value(mul_rv_integral.calculate_box(temp_box));
							mixed_boxes.push_back(temp_box);
						}
					}
				}
			}
		}

		boxes.clear();

		/*
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
		*/

		sort(mixed_boxes.begin(), mixed_boxes.end(), BoxFactory::compare_boxes_des);

		for(int i = 0; i < mixed_boxes.size(); i++)
		{
			boxes.push_back(mixed_boxes.at(i));
		}
		mixed_boxes.clear();
	}
	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| Probability interval         | Precision    | Required precision | Total time       |" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| [" << setprecision(12) << scientific << P_lower.leftBound() << ", " << P_upper.rightBound() << "] | " << P_upper.rightBound() - P_lower.leftBound() << " | " << settings["precision"].c_str() << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec |" << endl;
	cout << "|-------------------------------------------------------------------------------------|" << endl;
}

/*
void check_template(char* argv[])
{
	FileParser file_parser(argv[1]);
	std::map<string, string> settings = file_parser.get_settings();
	vector<RV*> rv = file_parser.get_rv();
	vector<string> temp = file_parser.get_temp();
	vector<string> temp_inv = file_parser.get_temp_inv();

	cout << "TEMPLATE:" << endl;
	for (int i = 0; i < temp.size(); i++)
	{
		cout << i << "). " << temp.at(i) << endl;
	}

	cout << "TEMPLATE_INV:" << endl;
	for (int i = 0; i < temp_inv.size(); i++)
	{
		cout << i << "). " << temp_inv.at(i) << endl;
	}
}
*/

int main(int argc, char* argv[])
{
	if(argc > 2)
	{
		if(regex_match(argv[2], regex("-alt")))
		{
			evaluate_and_branch(argv);
		}
		else
		{
			cout << "UNKNOWN FLAG \"" << argv[2] << "\"" << endl;
			return EXIT_FAILURE;
		}
	}
	else
	{
		branch_and_evaluate(argv);
	}
	//check_template(argv);
	
	return EXIT_SUCCESS;
}




