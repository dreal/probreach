//
// Created by kny on 4/11/18.
//

#ifndef PROBREACH_TRANSLATOR_UTIL_H
#define PROBREACH_TRANSLATOR_UTIL_H

#include <iterator>
#include <string>
#include <vector>

template <typename Out>
void split(const std::string &s, char delim, Out result);

std::vector<std::string> split(const std::string &s, char delim);

#endif //PROBREACH_TRANSLATOR_UTIL_H
