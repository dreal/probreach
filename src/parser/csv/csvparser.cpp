//
// Created by fedor on 04/03/16.
//

#include <fstream>
#include <string.h>
#include <easylogging++.h>
#include <pdrh_config.h>
#include <util/pdrh2box.h>
#include "csvparser.h"

using namespace std;

map<string, vector<pair<pdrh::node *, pdrh::node *>>>
csvparser::parse(string filename)
{
  ifstream file;
  map<string, vector<pair<pdrh::node *, pdrh::node *>>> result;
  map<string, vector<pdrh::node *>> noise_vector;
  file.open(filename.c_str());
  if (file.is_open())
  {
    CLOG_IF(global_config.verbose, INFO, "series-parser")
      << "Time series file: " << filename;
    string line;
    getline(file, line);

    //stripping the string
    line.erase(remove(line.begin(), line.end(), ' '), line.end());

    // fetching column names
    vector<string> cols, vars;
    string delimiter = ",";
    size_t pos = 0;
    while ((pos = line.find(delimiter)) != string::npos)
    {
      cols.push_back(line.substr(0, pos));
      line.erase(0, pos + delimiter.length());
    }
    cols.push_back(line.substr(0, line.length() - 1));

    // creating noise vector
    for (int i = 0; i < cols.size(); i++)
    {
      // var name
      string col = cols.at(i);
      // default noise value
      pdrh::node *noise = new pdrh::node(0.1);
      // default variable name
      string var_name = col;
      // checking if noise value is specified
      unsigned long col_pos = col.find_last_of(":");
      if (col_pos != string::npos)
      {
        var_name = col.substr(0, col_pos);
        noise = new pdrh::node(col.substr(col_pos + 1, col.length() - 1));
        if (pdrh2box::node_to_interval(noise).leftBound() <= 0)
        {
          CLOG(ERROR, "series-parser")
            << "Noise value for " << var_name << " should be positive";
          exit(EXIT_FAILURE);
        }
      }
      if (
        (strcmp(var_name.c_str(), "Mode") == 0) ||
        (strcmp(var_name.c_str(), "Step") == 0) ||
        (strcmp(var_name.c_str(), "Time") == 0))
      {
        noise = new pdrh::node(0);
      }
      noise_vector[var_name].push_back(noise);
      vars.push_back(var_name);
    }
    // fetching data
    while (getline(file, line))
    {
      for (int i = 0; i < vars.size() - 1; i++)
      {
        pos = line.find(delimiter);
        pdrh::node *value_node = new pdrh::node(line.substr(0, pos));
        pair<pdrh::node *, pdrh::node *> interval_node;
        if (
          (strcmp(vars.at(i).c_str(), "Time") != 0) &&
          (strcmp(vars.at(i).c_str(), "Mode") != 0) &&
          (strcmp(vars.at(i).c_str(), "Step") != 0) &&
          (!value_node->value.empty()))
        {
          interval_node = make_pair(
            new pdrh::node(
              "-",
              vector<pdrh::node *>{value_node, noise_vector[vars.at(i)].at(0)}),
            new pdrh::node(
              "+",
              vector<pdrh::node *>{
                value_node, noise_vector[vars.at(i)].at(0)}));
        }
        else
        {
          interval_node = make_pair(value_node, value_node);
        }
        result[vars.at(i)].push_back(interval_node);

        line.erase(0, pos + delimiter.length());
      }
      // last value in data
      pdrh::node *value_node = new pdrh::node(line.substr(0, pos));
      pair<pdrh::node *, pdrh::node *> interval_node;
      if (
        (strcmp(vars.at(vars.size() - 1).c_str(), "Time") != 0) &&
        (strcmp(vars.at(vars.size() - 1).c_str(), "Mode") != 0) &&
        (strcmp(vars.at(vars.size() - 1).c_str(), "Step") != 0) &&
        (!value_node->value.empty()))
      {
        interval_node = make_pair(
          new pdrh::node(
            "-",
            vector<pdrh::node *>{
              value_node, noise_vector[vars.at(vars.size() - 1)].at(0)}),
          new pdrh::node(
            "+",
            vector<pdrh::node *>{
              value_node, noise_vector[vars.at(vars.size() - 1)].at(0)}));
      }
      else
      {
        interval_node = make_pair(value_node, value_node);
      }
      result[vars.at(vars.size() - 1)].push_back(interval_node);
    }
  }
  else
  {
    CLOG(ERROR, "series-parser") << "Could not open file " << filename;
    exit(EXIT_FAILURE);
  }
  CLOG_IF(global_config.verbose, INFO, "series-parser")
    << "OK (" << result.cbegin()->second.size() << " rows; " << result.size()
    << " columns)";
  return result;
}