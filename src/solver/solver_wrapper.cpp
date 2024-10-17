//
// Created by fedor on 02/03/17.
//

#include <sstream>
#include <vector>
#include <stdexcept>
#include <fstream>
#include <map>
#include "solver_wrapper.h"
#include "dreal_wrapper.h"
#include "isat_wrapper.h"

using namespace std;

const string DREAL_NAME = "dReal";
const string ISAT_NAME = "iSAT";
const vector<string> ARGS = {"--version", "--help"};

solver::type parse_version_file(string filename)
{
  fstream output_file;
  output_file.open(filename.c_str());
  if (!output_file.is_open())
  {
    stringstream s;
    s << "Problem opening the file " << filename;
    throw runtime_error(s.str());
  }
  // getting the first the file
  string first_line;
  getline(output_file, first_line);
  output_file.close();
  remove(filename.c_str());
  if (first_line.find(DREAL_NAME) != string::npos)
  {
    return solver::DREAL;
  }
  else if (first_line.find(ISAT_NAME) != string::npos)
  {
    return solver::ISAT;
  }
  return solver::UNKNOWN_SOLVER;
}

solver::type solver::detect_solver(string path)
{
  string output(path + ".version");
  for (string args : ARGS)
  {
    stringstream s;
    s << path << " " << args << " 1> " << output;
    int res = system(s.str().c_str());
    if (res != 0)
    {
      stringstream e;
      e << "Unexpected problem running: " << s.str();
      throw runtime_error(e.str());
    }
    solver::type solver_type = parse_version_file(output);
    if (solver_type != solver::UNKNOWN_SOLVER)
    {
      return solver_type;
    }
  }
  return solver::UNKNOWN_SOLVER;
}

solver::output
solver::evaluate(string path, string input, string args, type solver_type)
{
  switch (solver_type)
  {
  case solver::DREAL:
    if (dreal::execute(path, input, args) == 0)
    {
      return solver::SAT;
    }
    return solver::UNSAT;

  case solver::ISAT:
    return isat::evaluate(path, input, args);

  default:
    stringstream s;
    s << "Solver type is not recognized";
    throw runtime_error(s.str());
  }
}