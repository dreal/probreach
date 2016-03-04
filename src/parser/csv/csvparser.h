//
// Created by fedor on 04/03/16.
//

#ifndef PROBREACH_CSVPARSER_H
#define PROBREACH_CSVPARSER_H

#include <capd/intervals/lib.h>
#include <map>

namespace csvparser
{
    std::map<std::string, std::vector<capd::interval>> parse(std::string);

    /*
    void display(std::map<string, vector<double> >, string);

    void display(std::map<string, vector<DInterval> >, string);
    */
}

#endif //PROBREACH_CSVPARSER_H


