//
// Created by kny on 05/06/18.
//

#include <iostream>
#include <sstream>
#include <iomanip>
#include <model.h>
#include "pdrh_config.h"
#include "model.h"

extern "C"
{
#include "pdrhparser.h"
}

#include "easylogging++.h"
#include "translator.h"

extern "C" int yyparse();
extern "C" FILE *yyin;

INITIALIZE_EASYLOGGINGPP

void parse_pdrh(string filename)
{
  CLOG_IF(global_config.verbose, INFO, "parser") << "Model file: " << filename;
  FILE *pdrhfile = fopen(filename.c_str(), "r");
  if (!pdrhfile)
  {
    CLOG(ERROR, "parser") << "Couldn't open " << filename;
    exit(EXIT_FAILURE);
  }
  std::stringstream s, pdrhnameprep;
  pdrhnameprep << filename << ".preprocessed";
  s << "cpp -w -P " << filename << " > " << pdrhnameprep.str().c_str();
  int res = system(s.str().c_str());
  // cheking the result of system call
  if (res != 0)
  {
    CLOG(ERROR, "parser") << "Problem occured while preprocessing " << filename;
    exit(EXIT_FAILURE);
  }
  // parsing the preprocessed file
  FILE *pdrhfileprep = fopen(pdrhnameprep.str().c_str(), "r");
  // make sure it's valid:
  if (!pdrhfileprep)
  {
    CLOG(ERROR, "parser") << "Couldn't open " << pdrhnameprep.str();
    exit(EXIT_FAILURE);
  }
  // set lex to read from it instead of defaulting to STDIN:
  yyin = pdrhfileprep;
  // parse through the input until there is no more:
  do
  {
    yyparse();
  } while (!feof(yyin));
  remove(pdrhnameprep.str().c_str());
  CLOG_IF(global_config.verbose, INFO, "parser") << "OK";
}

int main(int argc, char *argv[])
{
  START_EASYLOGGINGPP(argc, argv);
  el::Logger *parser_logger = el::Loggers::getLogger("parser");
  el::Logger *algorithm_logger = el::Loggers::getLogger("algorithm");
  el::Logger *solver_logger = el::Loggers::getLogger("solver");
  el::Logger *series_parser_logger = el::Loggers::getLogger("series-parser");
  el::Logger *config_parser_logger = el::Loggers::getLogger("config");
  el::Logger *rng_logger = el::Loggers::getLogger("ran_gen");
  el::Logger *model_logger = el::Loggers::getLogger("model");
  el::Logger *translator_logger = el::Loggers::getLogger("translator");

  // parse command line
  parse_pdrh_config(argc, argv);

  // setting precision on the output
  cout.precision(16);
  //cout << scientific;
  // pdrh parser
  parse_pdrh(global_config.model_filename);

  // setting the model type automatically here
  pdrh::set_model_type();

  // printing the model if the flag is set
  if (global_config.show_model)
  {
    cout << pdrh::model_to_string() << endl;
  }

  // runs the translator
  translator::translate();

  // unregister the loggers
  el::Loggers::unregisterLogger("parser");
  el::Loggers::unregisterLogger("algorithm");
  el::Loggers::unregisterLogger("solver");
  el::Loggers::unregisterLogger("series-parser");
  el::Loggers::unregisterLogger("config");
  el::Loggers::unregisterLogger("ran_gen");
  el::Loggers::unregisterLogger("model");
  el::Loggers::unregisterLogger("translator");
  return EXIT_SUCCESS;
}