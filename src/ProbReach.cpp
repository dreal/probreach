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
#include "Entry.h"
#include "Integral.h"
#include "Distribution.h"
#include "RV.h"
#include "CartesianProduct.h"

using namespace std;
using namespace capd;

double precision;
string modelFile = "";
string modelFileComplement = "";
string dReachOptions = "";
vector<string> drhTemplate;
vector<string> drhTemplateInverse;
bool verbose = false;

#ifdef _OPENMP
	omp_lock_t lock;
#endif

const regex normalRegEx("(\\s)*(N)(\\s)*(\\()([-+]?[0-9]*.?[0-9]+)(\\s)*(,)(\\s)*([-+]?[0-9]*.?[0-9]+)(\\s)*(\\))(\\s)*([a-zA-Z][a-zA-Z0-9_]*)(;)(\\s)*");
const regex uniformRegEx("(\\s)*(U)(\\s)*(\\()([-+]?[0-9]*.?[0-9]+)(\\s)*(,)(\\s)*([-+]?[0-9]*.?[0-9]+)(\\s)*(\\))(\\s)*([a-zA-Z][a-zA-Z0-9_]*)(;)(\\s)*");


/**
 * Takes name of pdrh template and return the drh
 * if rvIgnore is false then random variables are ignored
 */
void getTempFromFile(string filepath, vector<string> &temp, vector<RV> &rv)
{
	ifstream file;
	file.open(filepath.c_str());
	smatch matches;
	
	if(file.is_open())
	{
		string line;
		while (getline(file, line))
		{
			if (regex_match(line, matches, normalRegEx)) 
			{
				string param1 = string() + matches[5].str();
				double mean = atof(param1.c_str());
				string param2 = string() + matches[9].str();
				double deviation = atof(param2.c_str());
				string var = string() + matches[13].str();
				rv.push_back(RV("n", var, normalString(var, mean, deviation), mean - 20 * deviation, mean + 20 * deviation));
			} else
			if (regex_match(line, matches, uniformRegEx)) 
			{
				string param1 = string() + matches[5].str();
				double left = atof(param1.c_str());
				string param2 = string() + matches[9].str();
				double right =atof(param2.c_str());
				string var = string() + matches[13].str();
				rv.push_back(RV("u", var, uniformString(left, right), left, right));
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

/**
 * Takes name of pdrh template and return the drh
 * if rvIgnore is false then random variables are ignored
 */
void getTempFromFile(string filepath, vector<string> &temp)
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
		/*
		#ifdef _OPENMP
			omp_init_lock(&lock);
		#endif
		*/

		//adding the leftovers to the drh file
		for(int i = 0; i < temp.size(); i++)
		{
			drhFile << temp.at(i) << endl;
		}
		drhFile.close();
		/*
		#ifdef _OPENMP
     		omp_destroy_lock(&lock);
 		#endif
 		*/
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

	//string calldReach(calldReachStream.str());
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
			
			//DInterval result(1.0, 1.0);
			//for(int i = 0; i < 1; i++)
			//{
			//	result *= x.at(i).getPartialSum();
			//}	
			//return result;
			
			//return x.at(0).getPartialSum();
			#ifdef _OPENMP
    			omp_unset_lock(&lock);
   			#endif
			return true;
		}
		#ifdef _OPENMP
    		omp_unset_lock(&lock);
   		#endif
		//return DInterval(0.0, 0.0);
		return false;
	}
	else
	{
		cout << "COULD NOT OPEN THE FILE: " << outputFilepath << endl;
		#ifdef _OPENMP
    		omp_unset_lock(&lock);
   		#endif
	}

}


/**
 * Writes entries to the file
 *
 * @param entries entries to be stored in the file fileName
 */
void writeEntriesToFile(vector<Entry> entries, string fileName)
{
	ofstream file;
	file.open(fileName.c_str());
	if (file.is_open())
	{
		for (long int i = 0; i < entries.size(); i++)
		{
			file << i << ") " << entries.at(i).toString() << endl;
		}
		file.close();
	}
}



bool getSettings(string filename)
{
	ifstream settingsFile;
	settingsFile.open(filename.c_str());
	if (settingsFile.is_open())
	{
		while (!settingsFile.eof())
		{
			string line;
			getline(settingsFile, line);
			if (line == "param:")
			{
				getline(settingsFile, line);
				precision = atof(line.c_str());
				
			}
			if (line == "model:")
			{
				getline(settingsFile, modelFile);
				getline(settingsFile, modelFileComplement);
			}
						
			if (line == "dReach:")
			{
					while (!settingsFile.eof())
					{
						getline(settingsFile, line);
						smatch matches;
						regex depthRegex("(\\s)*([0-9]+)(\\s)*");
						if (regex_match(line, matches, depthRegex)) 
						{
							dReachOptions += matches[0];
						}
					}
					break;
			}
		}
		settingsFile.close();
		return true;		
	}
	return false;
}


int simulateNotParallel(int argc, char *argv[])
{
	if(!getSettings(argv[1]))
	{
		cout << "Invalid settings file" << endl;
		return EXIT_FAILURE;
	}

	if(argc > 2)
	{
		if((strcmp(argv[2], "--verbose") == 0) || (strcmp(argv[2], "-verbose") == 0))
		{
			verbose = true;
		}
	}

	vector<RV> rv;
	vector<string> temp;
	vector<string> tempInv;

	getTempFromFile(modelFile, temp, rv);
	getTempFromFile(modelFileComplement, tempInv);

	//printing out the rvs and templates
	/*
	cout << "Random variables " << endl;
	for (int i = 0; i < rv.size(); i++)
	{
		cout << rv.at(i).toString() << endl;
	}

	cout << "Template " << endl;
	for (int i = 0; i < temp.size(); i++)
	{
		cout << temp.at(i) << endl;
	}

	cout << "Inverted template " << endl;
	for (int i = 0; i < tempInv.size(); i++)
	{
		cout << tempInv.at(i) << endl;
	}
	*/

	
	//vector<RV> rv = getRVs(modelFile);
	if (rv.size() > 1)
	{
		cout << "WARNING!!! There are " << rv.size() << " random variables in the model. Only the first one will be considered" << endl;
	}
	
	double startTime = time(NULL);

	DInterval overIntg(0.0), underIntg(0.0), realIntg(0.0, 1.0), realIntgInf(0.0, 1.0);
	
	vector<Integral> integral;
	vector< vector<Entry> > vectors;
	vector<double> infError;
	
	Integral itg = Integral(rv.at(0), precision);
	DInterval I = itg.solve();
	vectors.push_back(itg.getEntries());
	integral.push_back(itg);
	infError.push_back(1 - I.leftBound());
		
	vector< vector<Entry> > cartProduct = cartesianProduct(vectors);
	
	vector<Entry> extraEntries;

	int counter = 0;
	
	//main loop	
	counter = 0;
	while (width(realIntg) > precision)
	{
		//going through all the vector<vector<Entry>>
		for (int i = 0; i < cartProduct.size(); i++)
		{
			if(verbose)
			{
				cout << counter << " of " << cartProduct.size()  << ") Interval: " << cartProduct.at(i).at(0).getSubInterval() << endl;
			}
			//cout << "NORMAL PROBLEM" << endl;
			//double delta = width(cartProduct.at(i).at(0).getSubInterval()) / 1000;
			if (dReach(rv, modelFile, temp, dReachOptions, cartProduct.at(i)))
			{	
				//cout << "CONVERTED PROBLEM" << endl;
				overIntg += cartProduct.at(i).at(0).getPartialSum();
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
				}
			}
			counter++;
		}

		cartProduct.clear();
		
		for (int i = 0; i < extraEntries.size(); i++)
		{
			vector<Entry> tmp;
			tmp.push_back(extraEntries.at(i));
			cartProduct.push_back(tmp);
		}		
		
		extraEntries.clear();

		realIntg = DInterval(underIntg.leftBound(), overIntg.rightBound());
		realIntgInf = DInterval(realIntg.leftBound(), realIntg.rightBound() + infError.at(0));
		
		if(verbose)
		{
			cout << "************" << endl;
			cout << "Division number " << counter << endl;
			cout << "underIntg: " << setprecision(16) << underIntg << endl;
			cout << "overIntg: " << setprecision(16) << overIntg << endl;
			cout << "realIntg: " << setprecision(16) << realIntg << endl;
			cout << "realIntgInf: " << setprecision(16) << realIntgInf << endl;	
		}

		overIntg = underIntg;
		counter = 0;
	}

	cout << endl;
	cout << "********************" << endl;
	cout << "RESULT:" << endl;
	cout << "P in " << setprecision(16) << realIntgInf << endl;
	cout << "Interval width = " << setprecision(16) << width(realIntgInf) << endl;
	cout << "Desired precision (epsilon) = " << precision << endl;
	cout << "Time: " << time(NULL) - startTime << endl;
	cout << "********************"<< endl;
	cout << endl;
	
	return EXIT_SUCCESS;
}

int simulatePartitionInParallel(int argc, char *argv[])
{
	
	if(!getSettings(argv[1]))
	{
		cout << "Invalid settings file" << endl;
		return EXIT_FAILURE;
	}

	if(argc > 2)
	{
		if((strcmp(argv[2], "--verbose") == 0) || (strcmp(argv[2], "-verbose") == 0))
		{
			verbose = true;
		}
	}
	
	vector<RV> rv;
	vector<string> temp;
	vector<string> tempInv;

	getTempFromFile(modelFile, temp, rv);
	getTempFromFile(modelFileComplement, tempInv);
	//cout << dReachOptions << endl;


	//printing out the rvs and templates
	/*
	cout << "Random variables " << endl;
	for (int i = 0; i < rv.size(); i++)
	{
		cout << rv.at(i).toString() << endl;
	}

	cout << "Template " << endl;
	for (int i = 0; i < temp.size(); i++)
	{
		cout << temp.at(i) << endl;
	}

	cout << "Inverted template " << endl;
	for (int i = 0; i < tempInv.size(); i++)
	{
		cout << tempInv.at(i) << endl;
	}
	*/

	
	//vector<RV> rv = getRVs(modelFile);
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
	#ifdef _OPENMP
    	omp_init_lock(&lock);
    	omp_set_num_threads(omp_get_max_threads() - 8);
 	#endif
    //cout.precision(12);
    cout << "Required precision: " << scientific << precision << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| Probability interval         | Precision    | Time per iteration | Total time       |" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| [" << setprecision(12) << scientific << underIntg.leftBound() << ", " << overIntg.rightBound() << "] | " << overIntg.rightBound() - underIntg.leftBound() << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec   | " << time(NULL) - startTime << " sec |" << endl;
	while (overIntg - underIntg > precision)
	{
		#pragma omp parallel
		{
			#pragma omp for
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
						extraEntries.push_back(cartProduct.at(i).at(0));
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

   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| Probability interval         | Precision    | Required precision | Total time       |" << endl;
   	cout << "|-------------------------------------------------------------------------------------|" << endl;
   	cout << "| [" << setprecision(12) << scientific << underIntg.leftBound() << ", " << overIntg.rightBound() << "] | " << overIntg.rightBound() - underIntg.leftBound() << " | " << precision << " | " << setprecision(0) << fixed << time(NULL) - startTime << " sec |" << endl;
	cout << "|-------------------------------------------------------------------------------------|" << endl;

	return EXIT_SUCCESS;
}

int main(int argc, char* argv[])
{
	//cout << "not in parallel" << endl;
	//simulateNotParallel(argc, argv);
	cout << "partition in parallel" << endl;
	simulatePartitionInParallel(argc, argv);
	return EXIT_SUCCESS;
}



