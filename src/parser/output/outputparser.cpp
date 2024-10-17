//
// Created by fedor on 20/01/17.
//

#include <iomanip>
#include "outputparser.h"

using namespace std;

map<box, capd::interval> outputparser::parse_p_map(string filename)
{
  ifstream file;
  file.open(filename.c_str());
  map<box, capd::interval> res_map;
  if (file.is_open())
  {
    string line;
    string p_delimiter = "|";
    while (getline(file, line))
    {
      // removing whitespaces
      line.erase(remove_if(line.begin(), line.end(), ::isspace), line.end());
      size_t pos = 0;
      pos = line.find(p_delimiter);
      string box_string, p_string;
      if (pos == string::npos)
      {
        cerr << "Could not locate probability enclosure in line: " << line
             << endl;
        exit(EXIT_FAILURE);
      }
      box_string = line.substr(0, pos);
      p_string = line.substr(pos + p_delimiter.length(), line.length() - pos);
      pos = p_string.find(",");
      if (pos == string::npos)
      {
        cerr << "Could not parse probability enclosure: " << p_string << endl;
        exit(EXIT_FAILURE);
      }
      res_map.insert(make_pair(
        box(box_string),
        capd::interval(
          p_string.substr(1, pos - 1),
          p_string.substr(pos + 1, p_string.length() - pos - 2))));
    }
  }
  else
  {
    cerr << "Could not open file " << filename << endl;
    exit(EXIT_FAILURE);
  }
  return res_map;
}