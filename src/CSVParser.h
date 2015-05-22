#ifndef CSVPARSER_H
#define CSVPARSER_H

#include<string>
#include<map>
#include<vector>
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>

using namespace std;
using namespace capd;

// Box class declaration
class CSVParser
{
private:

public:

    static std::map<string, vector<DInterval> > parse(string);

    static void display(std::map<string, vector<double> >, string);

    static void display(std::map<string, vector<DInterval> >, string);

};
#endif