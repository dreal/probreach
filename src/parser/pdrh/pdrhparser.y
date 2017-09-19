%{
#include <cstdio>
#include <iostream>
#include <string>
#include <string.h>
#include <sstream>
#include <cmath>
#include <limits>
#include <capd/capdlib.h>
#include <capd/intervals/lib.h>
#include "pdrh.h"
#include "measure.h"
#include "pdrh_config.h"

// stuff from flex that bison needs to know about:
extern "C" int yylex();
extern "C" int yyparse();
extern "C" FILE *yyin;
extern int line_num;

void yyerror(const char *s);

%}

%union
{
	int                         ival;
	float                       fval;
	char*                       sval;
    pdrh::node*                 nval;
    std::vector<pdrh::node*>*   nval_list;
}

// terminals
%token MODEL TIME
%token PDF N_DIST U_DIST E_DIST G_DIST DD_DIST
%token INFTY

%token MODE INVT FLOW JUMP INIT GOAL SYNTHESIZE TIME_PREC PATHS
%token D_DT TRANS PRIME

%token SQRT EXP LOG SIN COS TAN ASIN ACOS ATAN ABS
%token NOT AND OR XOR IMPLY
%token PLUS MINUS TIMES DIVIDE POWER
%token EQ GT LT GE LE NE
%token TRUE FALSE

%token <sval> m_type
%token <sval> identifier
%token <sval> number
%token <fval> n_float
%token <ival> n_int

%left EQ LT GT LE GE NE
%left PLUS MINUS
%left TIMES DIVIDE
%precedence UMINUS UPLUS
%right POWER

%type<sval> reset_var
%type<nval_list> props
%type<nval> pdf_expr prop expr arthm_expr pdf_bound

// to compile
//bison -d -o pdrhparser.c pdrhparser.y && flex -o pdrhlexer.c pdrhlexer.l && g++ -O2 -std=c++11 `/home/fedor/dreal3/build/release/bin/capd-config --cflags` pdrhparser.h pdrhparser.c pdrhlexer.c ../../model.cpp -lfl `/home/fedor/dreal3/build/release/bin/capd-config --libs` -o pdrh && ./pdrh ../../test/parser/test1.pdrh

// declaring some variables
%{
pdrh::mode *cur_mode = new pdrh::mode;
pdrh::mode::jump *cur_jump = new pdrh::mode::jump;
std::vector<pdrh::state> cur_states;
std::vector<pdrh::mode*> cur_path;
std::map<pdrh::node*, pdrh::node*> cur_dd;
%}

%%
pdrh:
	declarations modes init synthesize  {
	                                        pdrh::model_type = pdrh::PSY;
	                                    }
    | declarations modes init goal paths { ; }
	| declarations modes init goal      {
	                                        // we try to identify the model type automatically here
	                                        //pdrh::model_type = pdrh::HA;
	                                    }
	| model declarations modes init goal { ; }
	| model declarations modes init goal paths { ; }

model:
	MODEL ':' m_type ';'    {
	                                if(strcmp(strdup($3), "ha") == 0)
	                                {
	                                    pdrh::model_type = pdrh::HA;
	                                }
	                                else if(strcmp(strdup($3), "pha") == 0)
	                                {
	                                    pdrh::model_type = pdrh::PHA;
	                                }
	                                else if(strcmp(strdup($3), "nha") == 0)
                                    {
                                        pdrh::model_type = pdrh::NHA;
                                    }
                                    else if(strcmp(strdup($3), "npha") == 0)
                                    {
                                        pdrh::model_type = pdrh::NPHA;
                                    }
                                    else if(strcmp(strdup($3), "psy") == 0)
                                    {
                                        pdrh::model_type = pdrh::PSY;
                                    }
	                            }

declarations:
	declarations declaration { ; }
	| declaration { ; }

declaration:
	var_declaration { ; }
	| dist_declaration { ; }

var_declaration:
	'[' arthm_expr ',' arthm_expr ']' identifier ';'    {
	                                                        if(!pdrh::var_exists($6))
                                                            {
                                                                pdrh::push_var($6, $2, $4);
                                                            }
                                                            else
                                                            {
                                                               std::stringstream s;
                                                               s << "multiple declaration of variable \"" << $6 << "\"";
                                                               yyerror(s.str().c_str());
                                                            }
                                                        }
	| '[' arthm_expr ']' identifier ';'	                {
                                                            if(!pdrh::var_exists($4))
                                                            {
                                                               pdrh::push_var($4, $2, $2);
                                                            }
                                                            else
                                                            {
                                                               std::stringstream s;
                                                               s << "multiple declaration of variable \"" << $4 << "\"";
                                                               yyerror(s.str().c_str());
                                                            }
                                                        }
	| '[' arthm_expr ',' arthm_expr ']' TIME ';'        { pdrh::push_time_bounds($2, $4); }

dist_declaration:
    PDF '(' pdf_expr ',' pdf_bound ',' pdf_bound ',' arthm_expr ')' identifier ';'
                                                                                {
                                                                                    if(!pdrh::var_exists($11))
                                                                                    {
                                                                                        pdrh::push_var($11, $5, $7);
                                                                                        pdrh::push_rv($11, $3, $5, $7, $9);
                                                                                        if(global_config.stat_flag)
                                                                                        {
                                                                                            std::stringstream s;
                                                                                            s << "user-defined distribution for \"" << $11 << "\" is not supported in sampling mode";
                                                                                            yyerror(s.str().c_str());
                                                                                        }
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                       std::stringstream s;
                                                                                       s << "multiple declaration of variable \"" << $11 << "\"";
                                                                                       yyerror(s.str().c_str());
                                                                                    }
                                                                                }
    | G_DIST '(' arthm_expr ',' arthm_expr ')' identifier ';'                   {
                                                                                    if(!pdrh::var_exists($7))
                                                                                    {
                                                                                        pdrh::push_var($7, pdrh::push_terminal_node("-infty"),
                                                                                                                            pdrh::push_terminal_node("infty"));
                                                                                        pdrh::distribution::push_gamma($7, $3, $5);
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                       std::stringstream s;
                                                                                       s << "multiple declaration of variable \"" << $7 << "\"";
                                                                                       yyerror(s.str().c_str());
                                                                                    }
                                                                                }
    | N_DIST '(' arthm_expr ',' arthm_expr ')' identifier ';'                   {
                                                                                    if(!pdrh::var_exists($7))
                                                                                    {
                                                                                        pdrh::push_var($7, pdrh::push_terminal_node("-infty"), pdrh::push_terminal_node("infty"));
                                                                                        pdrh::push_rv($7, pdrh::distribution::normal_to_node($7, $3, $5),
                                                                                                        pdrh::push_terminal_node("-infty"), pdrh::push_terminal_node("infty"), $3);
                                                                                        pdrh::distribution::push_normal($7, $3, $5);
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                       std::stringstream s;
                                                                                       s << "multiple declaration of variable \"" << $7 << "\"";
                                                                                       yyerror(s.str().c_str());
                                                                                    }
                                                                                }
    | U_DIST '(' arthm_expr ',' arthm_expr ')' identifier ';'                   {
                                                                                    if(!pdrh::var_exists($7))
                                                                                    {
                                                                                        pdrh::push_var($7, $3, $5);
                                                                                        pdrh::push_rv($7, pdrh::distribution::uniform_to_node($3, $5), $3, $5, $3);
                                                                                        pdrh::distribution::push_uniform($7, $3, $5);
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                       std::stringstream s;
                                                                                       s << "multiple declaration of variable \"" << $7 << "\"";
                                                                                       yyerror(s.str().c_str());
                                                                                    }
                                                                                }
    | E_DIST '(' arthm_expr ')' identifier ';'                                  {
                                                                                    if(!pdrh::var_exists($5))
                                                                                    {
                                                                                        pdrh::push_var($5, pdrh::push_terminal_node("0"), pdrh::push_terminal_node("infty"));
                                                                                        pdrh::push_rv($5, pdrh::distribution::exp_to_node($5, $3),
                                                                                                                  pdrh::push_terminal_node("0"), pdrh::push_terminal_node("infty"),
                                                                                                                    pdrh::push_terminal_node("0"));
                                                                                        pdrh::distribution::push_exp($5, $3);
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                       std::stringstream s;
                                                                                       s << "multiple declaration of variable \"" << $5 << "\"";
                                                                                       yyerror(s.str().c_str());
                                                                                    }
                                                                                }
    | DD_DIST '(' dd_pairs ')' identifier ';'                                   {
                                                                                    if(!pdrh::var_exists($5))
                                                                                    {
                                                                                        pdrh::push_var($5, pdrh::push_terminal_node("-infty"), pdrh::push_terminal_node("infty"));
                                                                                        pdrh::push_dd($5, cur_dd);
                                                                                        cur_dd.clear();
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                       std::stringstream s;
                                                                                       s << "multiple declaration of variable \"" << $5 << "\"";
                                                                                       yyerror(s.str().c_str());
                                                                                    }
                                                                                }

pdf_bound:
    arthm_expr 		{ $$ = $1; }
    | INFTY 		{ $$ = pdrh::push_terminal_node("infty"); }
    | MINUS INFTY 	{ $$ = pdrh::push_terminal_node("-infty"); }

pdf_expr:
    identifier                      {
                                        $$ = pdrh::push_terminal_node($1);
                                    }
    | number                        {
                                        $$ = pdrh::push_terminal_node($1);
                                    }
    | MINUS pdf_expr %prec UMINUS   {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($2);
                                        $$ = pdrh::push_operation_node("-", operands);
                                    }
    | PLUS pdf_expr %prec UPLUS     {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($2);
                                        $$ = pdrh::push_operation_node("+", operands);
                                    }
    | pdf_expr MINUS pdf_expr       {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($1);
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("-", operands);
                                    }
    | pdf_expr PLUS pdf_expr        {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($1);
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("+", operands);
                                    }
    | pdf_expr TIMES pdf_expr       {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($1);
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("*", operands);
                                    }
    | pdf_expr DIVIDE pdf_expr      {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($1);
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("/", operands);
                                    }
    | pdf_expr POWER pdf_expr       {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($1);
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("^", operands);
                                    }
    | ABS '(' pdf_expr ')'          {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("abs", operands);
                                    }
    | SQRT '(' pdf_expr ')'         {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("sqrt", operands);
                                    }
    | EXP '(' pdf_expr ')'          {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("exp", operands);
                                    }
    | LOG '(' pdf_expr ')'          {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("log", operands);
                                    }
    | SIN '(' pdf_expr ')'          {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("sin", operands);
                                    }
    | COS '(' pdf_expr ')'          {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("cos", operands);
                                    }
    | TAN '(' pdf_expr ')'          {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("tan", operands);
                                    }
    | ASIN '(' pdf_expr ')'         {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("asin", operands);
                                    }
    | ACOS '(' pdf_expr ')'         {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("acos", operands);
                                    }
    | ATAN '(' pdf_expr ')'         {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("atan", operands);
                                    }
    | '(' pdf_expr ')'              {
                                        $$ = $2;
                                    }
    ;

dd_pairs:
    dd_pairs ',' dd_pair { ; }
    | dd_pair { ; }

dd_pair:
    arthm_expr ':' arthm_expr   {
                                    cur_dd.insert(std::make_pair($1, $3));
                                    //delete($1); delete($3);
                                }

modes:
	modes mode  { ; }
	| mode      { ; }

mode:
	'{' MODE number ';' invt flow jumps_section '}'              {
	                                                                if(pdrh::get_mode(atoi($3)) == NULL)
	                                                                {
                                                                        cur_dd.clear();
                                                                        cur_mode->id = atoi($3);
                                                                        cur_mode->time = pdrh::time;
                                                                        pdrh::push_mode(*cur_mode);
                                                                        delete cur_mode;
                                                                        cur_mode = new pdrh::mode;
                                                                    }
                                                                    else
                                                                    {
                                                                        std::stringstream s;
                                                                        s << "multiple declaration of mode \"" << $3 << "\"";
                                                                        yyerror(s.str().c_str());
                                                                    }
                                                                }
	| '{' MODE number ';' flow jumps_section '}'                {
	                                                                if(pdrh::get_mode(atoi($3)) == NULL)
                                                                    {
                                                                        cur_dd.clear();
                                                                        cur_mode->id = atoi($3);
                                                                        cur_mode->time = pdrh::time;
                                                                        pdrh::push_mode(*cur_mode);
                                                                        delete cur_mode;
                                                                        cur_mode = new pdrh::mode;
                                                                    }
                                                                    else
                                                                    {
                                                                        std::stringstream s;
                                                                        s << "multiple declaration of mode \"" << $3 << "\"";
                                                                        yyerror(s.str().c_str());
                                                                    }
                                                                }
	| '{' MODE number ';' timeprec flow jumps_section '}'       {
	                                                                if(pdrh::get_mode(atoi($3)) == NULL)
                                                                    {
                                                                        cur_dd.clear();
                                                                        cur_mode->id = atoi($3);
                                                                        cur_mode->time = pdrh::time;
                                                                        pdrh::push_mode(*cur_mode);
                                                                        delete cur_mode;
                                                                        cur_mode = new pdrh::mode;
                                                                    }
                                                                    else
                                                                    {
                                                                        std::stringstream s;
                                                                        s << "multiple declaration of mode \"" << $3 << "\"";
                                                                        yyerror(s.str().c_str());
                                                                    }
                                                                }
	| '{' MODE number ';' timeprec invt flow jumps_section '}'  {
	                                                                if(pdrh::get_mode(atoi($3)) == NULL)
                                                                    {
                                                                        cur_dd.clear();
                                                                        cur_mode->id = atoi($3);
                                                                        cur_mode->time = pdrh::time;
                                                                        pdrh::push_mode(*cur_mode);
                                                                        delete cur_mode;
                                                                        cur_mode = new pdrh::mode;
                                                                    }
                                                                    else
                                                                    {
                                                                        std::stringstream s;
                                                                        s << "multiple declaration of mode \"" << $3 << "\"";
                                                                        yyerror(s.str().c_str());
                                                                    }
                                                                }
    | '{' MODE number ';' TIME ':' '[' expr ',' expr ']' ';' flow jumps_section '}'
                                                                {
                                                                    if(pdrh::get_mode(atoi($3)) == NULL)
                                                                    {
                                                                        cur_dd.clear();
                                                                        cur_mode->id = atoi($3);
                                                                        cur_mode->time = make_pair($8, $10);
                                                                        pdrh::push_mode(*cur_mode);
                                                                        delete cur_mode;
                                                                        cur_mode = new pdrh::mode;
                                                                    }
                                                                    else
                                                                    {
                                                                        std::stringstream s;
                                                                        s << "multiple declaration of mode \"" << $3 << "\"";
                                                                        yyerror(s.str().c_str());
                                                                    }
                                                                }
    | '{' MODE number ';' TIME ':' '[' expr ',' expr ']' ';'  invt flow jumps_section '}'
                                                                {
                                                                    if(pdrh::get_mode(atoi($3)) == NULL)
                                                                    {
                                                                        cur_dd.clear();
                                                                        cur_mode->id = atoi($3);
                                                                        cur_mode->time = make_pair($8, $10);
                                                                        pdrh::push_mode(*cur_mode);
                                                                        delete cur_mode;
                                                                        cur_mode = new pdrh::mode;
                                                                    }
                                                                    else
                                                                    {
                                                                        std::stringstream s;
                                                                        s << "multiple declaration of mode \"" << $3 << "\"";
                                                                        yyerror(s.str().c_str());
                                                                    }
                                                                }

timeprec:
	TIME_PREC ':' number ';' { ; }

invt:
	INVT ':' prop_list { ; }
	| INVT ':'

prop_list:
	prop_list prop ';'  {
	                        pdrh::push_invt(*cur_mode, $2);
                        }
	| prop ';'          {
	                        pdrh::push_invt(*cur_mode, $1);
	                    }
props:
	props prop              {
	                            $$->push_back($2);
	                        }
	| prop                  {
	                            $$ = new std::vector<pdrh::node*>;
	                            $$->push_back($1);
	                        }

prop:
    expr EQ expr            {
                                std::vector<pdrh::node*> operands;
                                operands.push_back($1);
                                operands.push_back($3);
                                $$ = pdrh::push_operation_node("=", operands);
                            }
    | expr GT expr          {
                                std::vector<pdrh::node*> operands;
                                operands.push_back($1);
                                operands.push_back($3);
                                $$ = pdrh::push_operation_node(">", operands);
                            }
    | expr LT expr          {
                                std::vector<pdrh::node*> operands;
                                operands.push_back($1);
                                operands.push_back($3);
                                $$ = pdrh::push_operation_node("<", operands);
                            }
    | expr GE expr          {
                                std::vector<pdrh::node*> operands;
                                operands.push_back($1);
                                operands.push_back($3);
                                $$ = pdrh::push_operation_node(">=", operands);
                            }
    | expr LE expr          {
                                std::vector<pdrh::node*> operands;
                                operands.push_back($1);
                                operands.push_back($3);
                                $$ = pdrh::push_operation_node("<=", operands);
                            }
    | expr NE expr          {
                                std::vector<pdrh::node*> operands;
                                operands.push_back($1);
                                operands.push_back($3);
                                $$ = pdrh::push_operation_node("!=", operands);
                            }
    | TRUE                  {
                                $$ = pdrh::push_terminal_node("(true)");
                            }
    | FALSE                 {
                                $$ = pdrh::push_terminal_node("(false)");
                            }
    | '(' prop ')'          {
                                $$ = $2;
                            }
    | NOT prop              {
                                std::vector<pdrh::node*> operands;
                                operands.push_back($2);
                                $$ = pdrh::push_operation_node("not", operands);
                            }
    | '(' AND props ')'     {
                                $$ = pdrh::push_operation_node("and", *($3));
                            }
    | '(' OR props ')'      {
                                $$ = pdrh::push_operation_node("or", *($3));
                            }
    | '(' XOR props ')'     {
                                $$ = pdrh::push_operation_node("xor", *($3));
                            }
    | '(' IMPLY prop prop ')'   {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    operands.push_back($4);
                                    $$ = pdrh::push_operation_node("=>", operands);
                                }

flow:
	FLOW ':' odes { ; }

odes:
	odes ode { ; }
	| ode { ; }

ode:
	D_DT '[' identifier ']' EQ expr ';'     {
	                                            pdrh::push_ode(*cur_mode, strdup($3), $6);
	                                            free($3);
	                                        }

expr:
    identifier                  {
                                    if(pdrh::var_exists($1))
                                    {
                                        $$ = pdrh::push_terminal_node($1);
                                    }
                                    else
                                    {
                                        std::stringstream s;
                                        s << "undefined variable \"" << $1 << "\"";
                                        yyerror(s.str().c_str());
                                    }
                                }
    | number                    {
                                    $$ = pdrh::push_terminal_node($1);
                                }
    | MINUS expr %prec UMINUS   {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($2);
                                    $$ = pdrh::push_operation_node("-", operands);
                                }
    | PLUS expr %prec UPLUS     {
                                    $$ = $2;
                                }
    | expr MINUS expr           {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($1);
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("-", operands);
                                }
    | expr PLUS expr            {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($1);
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("+", operands);
                                }
    | expr TIMES expr           {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($1);
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("*", operands);
                                }
    | expr DIVIDE expr          {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($1);
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("/", operands);
                                }
    | expr POWER expr           {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($1);
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("^", operands);
                                }
    | ABS '(' expr ')'          {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("abs", operands);
                                }
    | SQRT '(' expr ')'         {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    operands.push_back(pdrh::push_terminal_node("0.5"));
                                    $$ = pdrh::push_operation_node("^", operands);
                                }
    | EXP '(' expr ')'          {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("exp", operands);
                                }
    | LOG '(' expr ')'          {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("log", operands);
                                }
    | SIN '(' expr ')'          {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("sin", operands);
                                }
    | COS '(' expr ')'          {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("cos", operands);
                                }
    | TAN '(' expr ')'          {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("tan", operands);
                                }
    | ASIN '(' expr ')'         {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("asin", operands);
                                }
    | ACOS '(' expr ')'         {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("acos", operands);
                                }
    | ATAN '(' expr ')'         {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("atan", operands);
                                }
    | '(' expr ')'              {
                                    $$ = $2;
                                }
    ;

arthm_expr:
    number                      {
                                    $$ = pdrh::push_terminal_node($1);
                                }
    | MINUS arthm_expr %prec UMINUS {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($2);
                                        $$ = pdrh::push_operation_node("-", operands);
                                    }
    | PLUS arthm_expr %prec UPLUS   {
                                        $$ = $2;
                                    }
    | arthm_expr MINUS arthm_expr   {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($1);
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("-", operands);
                                    }
    | arthm_expr PLUS arthm_expr    {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($1);
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("+", operands);
                                    }
    | arthm_expr TIMES arthm_expr   {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($1);
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("*", operands);
                                    }
    | arthm_expr DIVIDE arthm_expr  {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($1);
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("/", operands);
                                    }
    | arthm_expr POWER arthm_expr   {
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($1);
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("^", operands);
                                    }
    | ABS '(' arthm_expr ')'    {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("abs", operands);
                                }
    | SQRT '(' arthm_expr ')'   {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    operands.push_back(pdrh::push_terminal_node("0.5"));
                                    $$ = pdrh::push_operation_node("^", operands);
                                }
    | EXP '(' arthm_expr ')'    {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("exp", operands);
                                }
    | LOG '(' arthm_expr ')'    {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("log", operands);
                                }
    | SIN '(' arthm_expr ')'    {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("sin", operands);
                                }
    | COS '(' arthm_expr ')'    {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("cos", operands);
                                }
    | TAN '(' arthm_expr ')'    {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("tan", operands);
                                }
    | ASIN '(' arthm_expr ')'   {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("asin", operands);
                                }
    | ACOS '(' arthm_expr ')'   {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("acos", operands);
                                }
    | ATAN '(' arthm_expr ')'   {
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    $$ = pdrh::push_operation_node("atan", operands);
                                }
    | '(' arthm_expr ')'        {
                                    $$ = $2;
                                }
    ;

reset_props:
	reset_props reset_prop { ; }
	| reset_prop { ; }

reset_prop:
    reset_var EQ expr { pdrh::push_reset(*cur_mode, *cur_jump, $1, $3); }
    | TRUE { ; }
    | FALSE { ; }
    | '(' reset_prop ')' { ; }
    | '(' AND reset_props ')' { ; }

reset_var:
    identifier PRIME 	{
                            if(pdrh::var_exists($1))
                            {
                                $$ = $1;
                            }
                            else
                            {
                                std::stringstream s;
                                s << "undefined variable \"" << $1 << "\"";
                                yyerror(s.str().c_str());
                            }
						}
	;

reset_state:
	'@' number reset_prop ';'   {
	 	                            cur_jump->next_id = atoi($2);
	 	                            // updating resets
                                    // variables
                                    for(auto it = pdrh::var_map.begin(); it != pdrh::var_map.end(); it++)
                                    {
                                        if(cur_jump->reset.find(it->first) == cur_jump->reset.end())
                                        {
                                            cur_jump->reset.insert(make_pair(it->first, new pdrh::node(it->first)));
                                        }
                                    }
                                    // nondeterministic parameters
                                    for(auto it = pdrh::par_map.begin(); it != pdrh::par_map.end(); it++)
                                    {
                                        cur_jump->reset.insert(make_pair(it->first, new pdrh::node(it->first)));
                                    }
                                    // discrete random parameters
                                    for(auto it = pdrh::dd_map.begin(); it != pdrh::dd_map.end(); it++)
                                    {
                                        cur_jump->reset.insert(make_pair(it->first, new pdrh::node(it->first)));
                                    }
                                    // continuous random parameters
                                    for(auto it = pdrh::rv_map.begin(); it != pdrh::rv_map.end(); it++)
                                    {
                                        cur_jump->reset.insert(make_pair(it->first, new pdrh::node(it->first)));
                                    }
	 	                        }

jumps_section:
	JUMP ':' jumps { ; }
	| JUMP ':' { ; }

jumps:
	jumps jump { ; }
	| jump { ; }

jump:
	prop TRANS reset_state  {
	                            cur_jump->guard = $1;
	                            pdrh::push_jump(*cur_mode, *cur_jump);
	                            delete cur_jump;
	                            cur_jump = new pdrh::mode::jump;
	                        }

init:
	INIT ':' states     {
	                        delete cur_mode;
                         	delete cur_jump;
	                        pdrh::push_init(cur_states);
	                        cur_states.clear();
	                    }

goal:
	GOAL ':' states     {
	                        pdrh::push_goal(cur_states);
                            cur_states.clear();
                        }




paths:
    PATHS ':' path_list { ; }

path_list:
    path_list path ';'  {
                            pdrh::push_path(cur_path);
                            cur_path.clear();
                        }
    | path ';' {
                    pdrh::push_path(cur_path);
                    cur_path.clear();
               }
    ;

path:
    path ',' number {
                        pdrh::mode* m = pdrh::get_mode(atoi($3));
                        if(m == NULL)
                        {
                            std::stringstream s;
                            s << "mode \"" << $3 << "\" has not been defined";
                            yyerror(s.str().c_str());
                        }
                        else
                        {
                            cur_path.push_back(m);
                        }
                    }
    | number {
                pdrh::mode* m = pdrh::get_mode(atoi($1));
                if(m == NULL)
                {
                    std::stringstream s;
                    s << "mode \"" << $1 << "\" has not been defined";
                    yyerror(s.str().c_str());
                }
                else
                {
                    cur_path.push_back(m);
                }
             }
    ;



state:
	'@' number prop ';' {
	                        if(pdrh::get_mode(atoi($2)) != NULL)
                            {
                                pdrh::state *s = new pdrh::state;
                                s->id = atoi($2);
                                s->prop = $3;
                                cur_states.push_back(*s);
                                delete s;
	                        }
	                        else
	                        {
	                            std::stringstream s;
                                s << "mode \"" << $2 << "\" does not exist";
                                yyerror(s.str().c_str());
	                        }
	                    }

states:
	states state { ; }
	| state { ; }
	;

synthesize:
	SYNTHESIZE ':' syn_pairs { ; }

syn_pairs:
	syn_pairs syn_pair ';' { ; }
	| syn_pair ';' { ; }

syn_pair:
    identifier ':' arthm_expr   {
                                if(pdrh::var_exists($1))
                                {
                                    pdrh::push_syn_pair($1, $3);
                                }
                                else
                                {
                                   std::stringstream s;
                                   s << "undefined variable \"" << $1 << "\"";
                                   yyerror(s.str().c_str());
                                }
                            }

%%

void yyerror(const char *s)
{
	std::cerr << "line " << line_num << ": " << s << std::endl;
	exit(EXIT_FAILURE);
}
