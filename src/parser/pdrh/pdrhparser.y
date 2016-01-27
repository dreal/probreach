%{
#include <cstdio>
#include <iostream>
#include <string>
#include <string.h>
#include <sstream>
#include <cmath>
#include <limits>
#include "../../model.h"
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>

// stuff from flex that bison needs to know about:
extern "C" int yylex();
extern "C" int yyparse();
extern "C" FILE *yyin;
extern int line_num;

void yyerror(const char *s);
%}

%union {
	int ival;
	float fval;
	char* sval;
}

// terminals
%token MODEL TIME
%token PDF N_DIST U_DIST E_DIST G_DIST DD_DIST
%token INFTY

%token MODE INVT FLOW JUMP INIT GOAL SYNTHESIZE TIME_PREC
%token D_DT TRANS PRIME

%token SQRT EXP LOG SIN COS TAN ASIN ACOS ATAN ABS
%token NOT AND OR XOR IMPLY
%token PLUS MINUS TIMES DIVIDE POWER
%token EQ GT LT GE LE NE
%token TRUE FALSE

%token <sval> model_type
%token <sval> identifier
%token <fval> n_float
%token <ival> n_int

%left EQ LT GT LE GE NE
%left PLUS MINUS
%left TIMES DIVIDE
%precedence UMINUS UPLUS
%right POWER

%type<sval> reset_var
%type<sval> expr pdf_expr
%type<fval> number arthm_expr pdf_bound
%type<sval> prop props

// to compile
//bison -d -o pdrhparser.c pdrhparser.y && flex -o pdrhlexer.c pdrhlexer.l && g++ -O2 -std=c++11 `/home/fedor/dreal3/build/release/bin/capd-config --cflags` pdrhparser.h pdrhparser.c pdrhlexer.c ../../model.cpp -lfl `/home/fedor/dreal3/build/release/bin/capd-config --libs` -o pdrh && ./pdrh ../../test/parser/test1.pdrh

// declaring some variables
%{
pdrh::mode *cur_mode = new pdrh::mode;
pdrh::mode::jump *cur_jump = new pdrh::mode::jump;
std::vector<pdrh::state> cur_states;
std::map<capd::interval, capd::interval> cur_dd;
%}

%%
pdrh:
	declarations modes init synthesize { ; }
	| declarations modes init goal { ; }
	| model declarations modes init goal { ; }

model:
	MODEL ':' model_type ';' { ; }

declarations:
	declarations declaration { ; }
	| declaration { ; }

declaration:
	var_declaration { ; }
	| dist_declaration { ; }

var_declaration:
	'[' arthm_expr ',' arthm_expr ']' identifier ';'    {
	                                                        if(!pdrh::check_var($6))
                                                            {
                                                                pdrh::push_var($6, capd::interval($2, $4));
                                                            }
                                                            else
                                                            {
                                                               std::stringstream s;
                                                               s << "multiple declaration of variable \"" << $6 << "\"";
                                                               yyerror(s.str().c_str());
                                                            }
                                                        }
	| '[' arthm_expr ']' identifier ';'	                {
                                                            if(!pdrh::check_var($4))
                                                            {
                                                               pdrh::push_var($4, capd::interval($2, $2));
                                                            }
                                                            else
                                                            {
                                                               std::stringstream s;
                                                               s << "multiple declaration of variable \"" << $4 << "\"";
                                                               yyerror(s.str().c_str());
                                                            }
                                                        }
	| '[' arthm_expr ',' arthm_expr ']' TIME ';'        { pdrh::push_time_bounds(capd::interval($2, $4)); }

dist_declaration:
    PDF '(' pdf_expr ',' pdf_bound ',' pdf_bound ',' arthm_expr ')' identifier ';'
                                                                                {
                                                                                    if(!pdrh::check_var($11))
                                                                                    {
                                                                                        pdrh::push_var($11, capd::interval($5, $7));
                                                                                        pdrh::push_rv(strdup($11), strdup($3), capd::interval($5, $7), capd::interval($9));
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                       std::stringstream s;
                                                                                       s << "multiple declaration of variable \"" << $11 << "\"";
                                                                                       yyerror(s.str().c_str());
                                                                                    }
                                                                                }
    | G_DIST '(' arthm_expr ',' arthm_expr ')' identifier ';'                   {
                                                                                    if(!pdrh::check_var($7))
                                                                                    {
                                                                                        pdrh::push_var($7, capd::interval(-std::numeric_limits<double>::infinity(),
                                                                                                                            std::numeric_limits<double>::infinity()));
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                       std::stringstream s;
                                                                                       s << "multiple declaration of variable \"" << $7 << "\"";
                                                                                       yyerror(s.str().c_str());
                                                                                    }
                                                                                }
    | N_DIST '(' arthm_expr ',' arthm_expr ')' identifier ';'                   {
                                                                                    if(!pdrh::check_var($7))
                                                                                    {
                                                                                        pdrh::push_var($7, capd::interval(-std::numeric_limits<double>::infinity(),
                                                                                                                             std::numeric_limits<double>::infinity()));
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                       std::stringstream s;
                                                                                       s << "multiple declaration of variable \"" << $7 << "\"";
                                                                                       yyerror(s.str().c_str());
                                                                                    }
                                                                                }
    | U_DIST '(' arthm_expr ',' arthm_expr ')' identifier ';'                   {
                                                                                    if(!pdrh::check_var($7))
                                                                                    {
                                                                                        pdrh::push_var($7, capd::interval(-std::numeric_limits<double>::infinity(),
                                                                                                                             std::numeric_limits<double>::infinity()));
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                       std::stringstream s;
                                                                                       s << "multiple declaration of variable \"" << $7 << "\"";
                                                                                       yyerror(s.str().c_str());
                                                                                    }
                                                                                }
    | E_DIST '(' arthm_expr ')' identifier ';'                                  {
                                                                                    if(!pdrh::check_var($5))
                                                                                    {
                                                                                        pdrh::push_var($5, capd::interval(-std::numeric_limits<double>::infinity(),
                                                                                                                             std::numeric_limits<double>::infinity()));
                                                                                    }
                                                                                    else
                                                                                    {
                                                                                       std::stringstream s;
                                                                                       s << "multiple declaration of variable \"" << $5 << "\"";
                                                                                       yyerror(s.str().c_str());
                                                                                    }
                                                                                }
    | DD_DIST '(' dd_pairs ')' identifier ';'                                   {
                                                                                    if(!pdrh::check_var($5))
                                                                                    {
                                                                                        pdrh::push_var($5, capd::interval(-std::numeric_limits<double>::infinity(),
                                                                                                                             std::numeric_limits<double>::infinity()));
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
    | INFTY 		{ $$ = +std::numeric_limits<double>::infinity(); }
    | MINUS INFTY 	{ $$ = -std::numeric_limits<double>::infinity(); }

pdf_expr:
    identifier                      {
                                        $$ = $1;
                                    }
    | number                        {
                                        std::stringstream s;
                                        s << $1;
                                        $$ = strdup(s.str().c_str());
                                    }
    | MINUS pdf_expr %prec UMINUS   {
                                        std::stringstream s;
                                        s << "-" << $2;
                                        $$ = strdup(s.str().c_str());
                                    }
    | PLUS pdf_expr %prec UPLUS     {
                                        $$ = $2;
                                    }
    | pdf_expr MINUS pdf_expr       {
                                        std::stringstream s;
                                        s << $1 << "-" << $3;
                                        $$ = strdup(s.str().c_str());
                                    }
    | pdf_expr PLUS pdf_expr        {
                                        std::stringstream s;
                                        s << $1 << "+" << $3;
                                        $$ = strdup(s.str().c_str());
                                    }
    | pdf_expr TIMES pdf_expr       {
                                        std::stringstream s;
                                        s << $1 << "*" << $3;
                                        $$ = strdup(s.str().c_str());
                                    }
    | pdf_expr DIVIDE pdf_expr      {
                                        std::stringstream s;
                                        s << $1 << "/" << $3;
                                        $$ = strdup(s.str().c_str());
                                    }
    | pdf_expr POWER pdf_expr       {
                                        std::stringstream s;
                                        s << $1 << "^" << $3;
                                        $$ = strdup(s.str().c_str());
                                    }
    | ABS '(' pdf_expr ')'          {
                                        std::stringstream s;
                                        s << "abs(" << $3 << ")";
                                        $$ = strdup(s.str().c_str());
                                    }
    | SQRT '(' pdf_expr ')'         {
                                        std::stringstream s;
                                        s << $3 << "^0.5";
                                        $$ = strdup(s.str().c_str());
                                    }
    | EXP '(' pdf_expr ')'          {
                                        std::stringstream s;
                                        s << "exp(" << $3 << ")";
                                        $$ = strdup(s.str().c_str());
                                    }
    | LOG '(' pdf_expr ')'          {
                                        std::stringstream s;
                                        s << "log(" << $3 << ")";
                                        $$ = strdup(s.str().c_str());
                                    }
    | SIN '(' pdf_expr ')'          {
                                        std::stringstream s;
                                        s << "sin(" << $3 << ")";
                                        $$ = strdup(s.str().c_str());
                                    }
    | COS '(' pdf_expr ')'          {
                                        std::stringstream s;
                                        s << "cos(" << $3 << ")";
                                        $$ = strdup(s.str().c_str());
                                    }
    | TAN '(' pdf_expr ')'          {
                                        std::stringstream s;
                                        s << "tan(" << $3 << ")";
                                        $$ = strdup(s.str().c_str());
                                    }
    | ASIN '(' pdf_expr ')'         {
                                        std::stringstream s;
                                        s << "asin(" << $3 << ")";
                                        $$ = strdup(s.str().c_str());
                                    }
    | ACOS '(' pdf_expr ')'         {
                                        std::stringstream s;
                                        s << "acos(" << $3 << ")";
                                        $$ = strdup(s.str().c_str());
                                    }
    | ATAN '(' pdf_expr ')'         {
                                        std::stringstream s;
                                        s << "atan(" << $3 << ")";
                                        $$ = strdup(s.str().c_str());
                                    }
    | '(' pdf_expr ')'              {
                                        std::stringstream s;
                                        s << "(" << $2 << ")";
                                        $$ = strdup(s.str().c_str());
                                    }
    ;

dd_pairs:
    dd_pairs ',' dd_pair { ; }
    | dd_pair { ; }

dd_pair:
    arthm_expr ':' arthm_expr   {
                                    cur_dd.insert(std::make_pair(capd::interval($1), capd::interval($3)));
                                }

modes:
	modes mode  { ; }
	| mode      { ; }

mode:
	'{' MODE n_int ';' invt flow jumps_section '}'              {
                                                                    cur_mode->id = $3;
                                                                    pdrh::push_mode(*cur_mode);
                                                                    delete cur_mode;
                                                                    cur_mode = new pdrh::mode;
                                                                }
	| '{' MODE n_int ';' flow jumps_section '}'                 {
                                                                    cur_mode->id = $3;
                                                                    pdrh::push_mode(*cur_mode);
                                                                    delete cur_mode;
                                                                    cur_mode = new pdrh::mode;
                                                                }
	| '{' MODE n_int ';' timeprec flow jumps_section '}'        {
	                                                                cur_mode->id = $3;
                                                                    pdrh::push_mode(*cur_mode);
                                                                    delete cur_mode;
                                                                    cur_mode = new pdrh::mode;
                                                                }
	| '{' MODE n_int ';' timeprec invt flow jumps_section '}'   {
	                                                                cur_mode->id = $3;
                                                                    pdrh::push_mode(*cur_mode);
                                                                    delete cur_mode;
                                                                    cur_mode = new pdrh::mode;
                                                                }

timeprec:
	TIME_PREC ':' number ';' { ; }

invt:
	INVT ':' prop_list { ; }
	| INVT ':'

prop_list:
	prop_list prop ';'  {
	                        pdrh::push_invt(*cur_mode, strdup($2));
                          	free($2);
                        }
	| prop ';'          {
	                        pdrh::push_invt(*cur_mode, strdup($1));
	                        free($1);
	                    }
props:
	props prop              {
	                            std::stringstream s;
	                            s << $1 << " " << $2;
	                            $$ = strdup(s.str().c_str());
	                        }
	| prop                  { $$ = $1; }

prop:
    expr EQ expr            {
                                std::stringstream s;
                                s << "(= " << $1 << " " << $3 << ")";
                                $$ = strdup(s.str().c_str());
                            }
    | expr GT expr          {
                                std::stringstream s;
                                s << "(> " << $1 << " " << $3 << ")";
                                $$ = strdup(s.str().c_str());
                            }
    | expr LT expr          {
                                std::stringstream s;
                                s << "(< " << $1 << " " << $3 << ")";
                                $$ = strdup(s.str().c_str());
                            }
    | expr GE expr          {
                                std::stringstream s;
                                s << "(>= " << $1 << " " << $3 << ")";
                                $$ = strdup(s.str().c_str());
                            }
    | expr LE expr          {
                                std::stringstream s;
                                s << "(<= " << $1 << " " << $3 << ")";
                                $$ = strdup(s.str().c_str());
                            }
    | expr NE expr          {
                                std::stringstream s;
                                s << "(not (= " << $1 << " " << $3 << "))";
                                $$ = strdup(s.str().c_str());
                            }
    | TRUE                  {
                                std::stringstream s;
                                s << "(true)";
                                $$ = strdup(s.str().c_str());
                            }
    | FALSE                 {
                                std::stringstream s;
                                s << "(false)";
                                $$ = strdup(s.str().c_str());
                            }
    | '(' prop ')'          {
                                std::stringstream s;
                                s << "(" << $2 << ")";
                                $$ = strdup(s.str().c_str());
                            }
    | NOT prop              {
                                std::stringstream s;
                                s << "(not " << $2 << ")";
                                $$ = strdup(s.str().c_str());
                            }
    | '(' AND props ')'     {
                                std::stringstream s;
                                s << "(and " << $3 << ")";
                                $$ = strdup(s.str().c_str());
                            }
    | '(' OR props ')'      {
                                std::stringstream s;
                                s << "(or " << $3 << ")";
                                $$ = strdup(s.str().c_str());
                            }
    | '(' XOR props ')'     {
                                std::stringstream s;
                                s << "(xor " << $3 << ")";
                                $$ = strdup(s.str().c_str());
                            }
    | '(' IMPLY prop prop ')'   {
                                    std::stringstream s;
                                    s << "(=> " << $3 << " " << $4 << ")";
                                    $$ = strdup(s.str().c_str());
                                }

flow:
	FLOW ':' odes { ; }

odes:
	odes ode { ; }
	| ode { ; }

ode:
	D_DT '[' identifier ']' EQ expr ';'     {
	                                            pdrh::push_ode(*cur_mode, strdup($3), strdup($6));
	                                            free($3); free($6);
	                                        }

expr:
    identifier                  {
                                    if(pdrh::check_var($1))
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
    | number                    {
                                    std::stringstream s;
                                    s << $1;
                                    $$ = strdup(s.str().c_str());
                                }
    | MINUS expr %prec UMINUS   {
                                    std::stringstream s;
                                    s << "(- 0 " << $2 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | PLUS expr %prec UPLUS     {
                                    std::stringstream s;
                                    s << "(+ 0 " << $2 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | expr MINUS expr           {
                                    std::stringstream s;
                                    s << "(- " << $1 << " " << $3 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | expr PLUS expr            {
                                    std::stringstream s;
                                    s << "(+ " << $1 << " " << $3 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | expr TIMES expr           {
                                    std::stringstream s;
                                    s << "(* " << $1 << " " << $3 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | expr DIVIDE expr          {
                                    std::stringstream s;
                                    s << "(/ " << $1 << " " << $3 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | expr POWER expr           {
                                    std::stringstream s;
                                    s << "(^ " << $1 << " " << $3 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | ABS '(' expr ')'          {
                                    std::stringstream s;
                                    s << "(abs " << $3 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | SQRT '(' expr ')'         {
                                    std::stringstream s;
                                    s << "(^ " << $3 << " 0.5)";
                                    $$ = strdup(s.str().c_str());
                                }
    | EXP '(' expr ')'          {
                                    std::stringstream s;
                                    s << "(exp " << $3 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | LOG '(' expr ')'          {
                                    std::stringstream s;
                                    s << "(log " << $3 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | SIN '(' expr ')'          {
                                    std::stringstream s;
                                    s << "(sin " << $3 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | COS '(' expr ')'          {
                                    std::stringstream s;
                                    s << "(cos " << $3 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | TAN '(' expr ')'          {
                                    std::stringstream s;
                                    s << "(tan " << $3 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | ASIN '(' expr ')'         {
                                    std::stringstream s;
                                    s << "(asin " << $3 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | ACOS '(' expr ')'         {
                                    std::stringstream s;
                                    s << "(acos " << $3 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | ATAN '(' expr ')'         {
                                    std::stringstream s;
                                    s << "(atan " << $3 << ")";
                                    $$ = strdup(s.str().c_str());
                                }
    | '(' expr ')'              {
                                    $$ = $2;
                                }
    ;

arthm_expr:
	number 							{ $$ = $1; }
	| MINUS arthm_expr %prec UMINUS { $$ = -$2; }
	| PLUS arthm_expr %prec UPLUS 	{ $$ = $2; }
	| arthm_expr PLUS arthm_expr 	{ $$ = $1 + $3; }
	| arthm_expr MINUS arthm_expr 	{ $$ = $1 - $3; }
	| arthm_expr TIMES arthm_expr 	{ $$ = $1 * $3; }
	| arthm_expr DIVIDE arthm_expr 	{ $$ = $1 / $3; }
	| arthm_expr POWER arthm_expr 	{ $$ = std::pow($1, $3); }
	| ABS '(' arthm_expr ')' 		{ $$ = std::abs($3); }
	| SQRT '(' arthm_expr ')' 		{ $$ = std::sqrt($3); }
	| EXP '(' arthm_expr ')' 		{ $$ = std::exp($3); }
	| LOG '(' arthm_expr ')' 		{ $$ = std::log($3); }
	| SIN '(' arthm_expr ')' 		{ $$ = std::sin($3); }
	| COS '(' arthm_expr ')' 		{ $$ = std::cos($3); }
	| TAN '(' arthm_expr ')' 		{ $$ = std::tan($3); }
	| ASIN '(' arthm_expr ')' 		{ $$ = std::asin($3); }
	| ACOS '(' arthm_expr ')' 		{ $$ = std::acos($3); }
	| ATAN '(' arthm_expr ')' 		{ $$ = std::atan($3); }
	| '(' arthm_expr ')' 			{ $$ = $2; }
	;

reset_props:
	reset_props reset_prop { ; }
	| reset_prop { ; }

reset_prop:
    reset_var EQ expr { pdrh::push_reset(*cur_mode, *cur_jump, strdup($1), strdup($3)); }
    | TRUE { ; }
    | FALSE { ; }
    | '(' reset_prop ')' { ; }
    | '(' AND reset_props ')' { ; }

reset_var:
    identifier PRIME 	{
                            if(pdrh::check_var($1))
                            {
                                std::stringstream s;
                                s << $1 << "'";
                                $$ = strdup(s.str().c_str());
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
	'@' n_int reset_prop ';'    {
	 	                            cur_jump->next_id = $2;
	 	                        }

jumps_section:
	JUMP ':' jumps { ; }
	| JUMP ':' { ; }

jumps:
	jumps jump { ; }
	| jump { ; }

jump:
	prop TRANS reset_state  {
	                            cur_jump->guard = strdup($1);
	                            pdrh::push_jump(*cur_mode, *cur_jump);
	                            delete cur_jump;
	                            cur_jump = new pdrh::mode::jump;
	                        }

init:
	INIT ':' states     {
	                        pdrh::push_init(cur_states);
	                        cur_states.clear();
	                    }

goal:
	GOAL ':' states     {
	                        pdrh::push_goal(cur_states);
                            cur_states.clear();
                        }

state:
	'@' n_int prop ';'  {
	                        pdrh::state *s = new pdrh::state;
	                        s->id = $2;
	                        s->prop = strdup($3);
	                        cur_states.push_back(*s);
	                        delete s;
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
    identifier ':' number   {
                                if(pdrh::check_var($1))
                                {
                                    pdrh::push_syn_pair(strdup($1), capd::interval($3));
                                }
                                else
                                {
                                   std::stringstream s;
                                   s << "undefined variable \"" << $1 << "\"";
                                   yyerror(s.str().c_str());
                                }
                            }

number:
	n_float 			{ $$ = $1; }
	| n_int 			{ $$ = $1; }

%%

int main(int argc, char* argv[]) {

	std::cout << "Parsing " << argv[1];

	// open a file handle to a particular file:
	FILE *pdrhfile = fopen(argv[1], "r");
	// make sure it's valid:
	if (!pdrhfile) {
		std::cout << "I can't open " << argv[1] << std::endl;
		return -1;
	}

	std::stringstream s, pdrhnameprep;

	pdrhnameprep << argv[1] << ".preprocessed";

	s << "cpp -w -P " << argv[1] << " > " << pdrhnameprep.str().c_str();

	system(s.str().c_str());

	FILE *pdrhfileprep = fopen(pdrhnameprep.str().c_str(), "r");
    // make sure it's valid:
    if (!pdrhfileprep) {
    	std::cout << "I can't open " << pdrhnameprep << std::endl;
    	return -1;
    }

	// set lex to read from it instead of defaulting to STDIN:
	yyin = pdrhfileprep;

	// parse through the input until there is no more:
	do {
		yyparse();
	} while (!feof(yyin));

	std::remove(pdrhnameprep.str().c_str());
	std::cout << " --- OK" << std::endl;

	std::cout << pdrh::print_model() << std::endl;

	delete cur_mode;
	delete cur_jump;
	cur_states.clear();
    cur_dd.clear();
}

void yyerror(const char *s) {
	std::cout << " | parse error on line " << line_num << ": " << s << std::endl;
	// might as well halt now:
	exit(-1);
}
