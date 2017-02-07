%{
#include <cstdio>
#include <iostream>
#include <string>
#include <string.h>
#include <sstream>
#include <cmath>
#include <limits>
#include "model.h"
#include "mode.h"
#include "jump.h"
#include "node.h"
#include <map>

// stuff from flex that bison needs to know about:
extern int yylex();
extern int yyparse();
extern FILE *yyin;
extern int line_num;

void yyerror(const char *);

model pdrh_model;

%}

%union
{
	int                             ival;
	float                           fval;
	char*                           sval;
    node*                           nval;
    vector<node>*                   nlist;
    pair<string, node>*             npair;
    vector<pair<string, node>>*     npairlist;
    map<string, node>*              nmap;
    mode*                           mval;
    vector<mode>*                   mlist;
    jump*                           jval;
    vector<jump>*                   jlist;
    pair<int, map<string, node>>*   rstate;
    pair<int, node>*                spair;
    vector<pair<int, node>>*        spairlist;
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
%type<nlist> props prop_list invt
%type<nval> pdf_expr prop expr arthm_expr pdf_bound
%type<npair> ode reset_prop
%type<nmap> odes flow reset_props reset_prop_list
%type<mval> mode
%type<jval> jump
%type<jlist> jumps_section jumps
%type<rstate> reset_state
%type<spairlist> states
%type<spair> state

// declaring some variables
%{

%}

%%
pdrh:
	declarations modes init synthesize  { ; }
	| declarations modes init goal      { ; }
	| model declarations modes init goal { ; }

model:
	MODEL ':' m_type ';'    {
	                                if(strcmp(strdup($3), "ha") == 0) { ; }
	                                else if(strcmp(strdup($3), "pha") == 0) { ; }
	                                else if(strcmp(strdup($3), "nha") == 0) { ; }
                                    else if(strcmp(strdup($3), "npha") == 0) { ; }
                                    else if(strcmp(strdup($3), "psy") == 0) { ; }
                            }

declarations:
	declarations declaration    {

	                            }
	| declaration { ; }

declaration:
	var_declaration { ; }
	| dist_declaration { ; }

var_declaration:
	'[' arthm_expr ',' arthm_expr ']' identifier ';'    {
	                                                        pdrh_model.push_var($6, *$2, *$4);
	                                                    }
	| '[' arthm_expr ']' identifier ';'	                {
	                                                        pdrh_model.push_var($4, *$2, *$2);
	                                                    }
	| '[' arthm_expr ',' arthm_expr ']' TIME ';'        {
	                                                        pdrh_model.set_time(*$2, *$4);
	                                                    }

dist_declaration:
    PDF '(' pdf_expr ',' pdf_bound ',' pdf_bound ',' arthm_expr ')' identifier ';' { ; }
    | G_DIST '(' arthm_expr ',' arthm_expr ')' identifier ';'                   { ; }
    | N_DIST '(' arthm_expr ',' arthm_expr ')' identifier ';'                   { ; }
    | U_DIST '(' arthm_expr ',' arthm_expr ')' identifier ';'                   { ; }
    | E_DIST '(' arthm_expr ')' identifier ';'                                  { ; }
    | DD_DIST '(' dd_pairs ')' identifier ';'                                   { ; }

pdf_bound:
    arthm_expr 		{ $$ = $1; }
    | INFTY 		{ $$ = new node("infty"); }
    | MINUS INFTY 	{ $$ = new node("-infty"); }

pdf_expr:
    identifier                      {
                                        $$ = new node($1);
                                    }
    | number                        {
                                        $$ = new node($1);
                                    }
    | MINUS pdf_expr %prec UMINUS   {
                                        $$ = new node("-", vector<node>{*$2});
                                    }
    | PLUS pdf_expr %prec UPLUS     {
                                        $$ = new node("+", vector<node>{*$2});
                                    }
    | pdf_expr MINUS pdf_expr       {
                                        /*
                                        $$ = new node("-", vector<node>{ *$1,  }
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($1);
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("-", operands);
                                        */
                                    }
    | pdf_expr PLUS pdf_expr        {
                                        /*
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($1);
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("+", operands);
                                        */
                                    }
    | pdf_expr TIMES pdf_expr       {
                                        /*
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($1);
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("*", operands);
                                        */
                                    }
    | pdf_expr DIVIDE pdf_expr      {
                                        /*
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($1);
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("/", operands);
                                        */
                                    }
    | pdf_expr POWER pdf_expr       {
                                        /*
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($1);
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("^", operands);
                                        */
                                    }
    | ABS '(' pdf_expr ')'          {
                                        /*
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("abs", operands);
                                        */
                                    }
    | SQRT '(' pdf_expr ')'         {
                                        /*
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("sqrt", operands);
                                        */
                                    }
    | EXP '(' pdf_expr ')'          {
                                        /*
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("exp", operands);
                                        */
                                    }
    | LOG '(' pdf_expr ')'          {
                                        /*
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("log", operands);
                                        */
                                    }
    | SIN '(' pdf_expr ')'          {
                                        /*
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("sin", operands);
                                        */
                                    }
    | COS '(' pdf_expr ')'          {
                                        /*
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("cos", operands);
                                        */
                                    }
    | TAN '(' pdf_expr ')'          {
                                        /*
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("tan", operands);
                                        */
                                    }
    | ASIN '(' pdf_expr ')'         {
                                        /*
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("asin", operands);
                                        */
                                    }
    | ACOS '(' pdf_expr ')'         {
                                        /*
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("acos", operands);
                                        */
                                    }
    | ATAN '(' pdf_expr ')'         {
                                        /*
                                        std::vector<pdrh::node*> operands;
                                        operands.push_back($3);
                                        $$ = pdrh::push_operation_node("atan", operands);
                                        */
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
                                    //cur_dd.insert(std::make_pair($1, $3));
                                    //delete($1); delete($3);
                                }

modes:
	modes mode  {
	                pdrh_model.push_mode(*$2);
	            }
	| mode      {
	                pdrh_model.push_mode(*$1);
	            }

mode:
	'{' MODE number ';' invt flow jumps_section '}'             {
	                                                                $$ = new mode(atoi($3), *$5, *$6, *$7);
                                                                }
	| '{' MODE number ';' flow jumps_section '}'                {
	                                                                $$ = new mode(atoi($3), *$5, *$6);
                                                                }
	| '{' MODE number ';' timeprec flow jumps_section '}'       {

                                                                }
	| '{' MODE number ';' timeprec invt flow jumps_section '}'  {

                                                                }

timeprec:
	TIME_PREC ':' number ';' { ; }

invt:
	INVT ':' prop_list  {
	                        $$ = $3;
	                    }
	| INVT ':'          {
	                        $$ = new vector<node>();
	                    }

prop_list:
	prop_list prop ';'  {
	                        $$->push_back(*$2);
                        }
	| prop ';'          {
	                        $$ = new vector<node>();
                            $$->push_back(*$1);
	                    }
props:
	props prop              {
	                            $$->push_back(*$2);
	                        }
	| prop                  {
	                            $$ = new vector<node>();
	                            $$->push_back(*$1);
	                        }

prop:
    expr EQ expr            {
                                $$ = new node("=", vector<node>{*$1, *$3});
                            }
    | expr GT expr          {
                                $$ = new node(">", vector<node>{*$1, *$3});
                            }
    | expr LT expr          {
                                $$ = new node("<", vector<node>{*$1, *$3});
                            }
    | expr GE expr          {
                                $$ = new node(">=", vector<node>{*$1, *$3});
                            }
    | expr LE expr          {
                                $$ = new node("<=", vector<node>{*$1, *$3});
                            }
    | expr NE expr          {
                                $$ = new node("!=", vector<node>{*$1, *$3});
                            }
    | TRUE                  {
                                $$ = new node("(true)");
                            }
    | FALSE                 {
                                $$ = new node("(false)");
                            }
    | '(' prop ')'          {
                                $$ = $2;
                            }
    | NOT prop              {
                                $$ = new node("not", vector<node>{*$2});
                            }
    | '(' AND props ')'     {
                                $$ = new node("and", *$3);
                            }
    | '(' OR props ')'      {
                                $$ = new node("or", *$3);
                            }
    | '(' XOR props ')'     {
                                $$ = new node("xor", *$3);
                            }
    | '(' IMPLY prop prop ')'   {
                                    $$ = new node("=>", vector<node>{*$3, *$4});
                                }

flow:
	FLOW ':' odes   {
	                    $$ = $3;
	                }

odes:
	odes ode    {
	                $$->insert(*$2);
	            }
	| ode       {
	                $$ = new map<string, node>();
	                $$->insert(*$1);
	            }

ode:
	D_DT '[' identifier ']' EQ expr ';'     {
	                                            $$ = new pair<string, node>($3, *$6);
	                                        }

expr:
    identifier                  {
                                    if(pdrh_model.var_exists($1))
                                    {
                                        $$ = new node($1);
                                    }
                                    else
                                    {
                                        stringstream s;
                                        s << "undeclared variable \"" << $1 << "\"";
                                        yyerror(s.str().c_str());
                                    }
                                }
    | number                    {
                                    $$ = new node($1);
                                }
    | MINUS expr %prec UMINUS   {
                                    $$ = new node("-", vector<node>{*$2});
                                }
    | PLUS expr %prec UPLUS     {
                                    $$ = $2;
                                }
    | expr MINUS expr           {
                                    $$ = new node("-", vector<node>{*$1, *$3});
                                }
    | expr PLUS expr            {
                                    $$ = new node("+", vector<node>{*$1, *$3});
                                }
    | expr TIMES expr           {
                                    $$ = new node("*", vector<node>{*$1, *$3});
                                }
    | expr DIVIDE expr          {
                                    $$ = new node("/", vector<node>{*$1, *$3});
                                }
    | expr POWER expr           {
                                    $$ = new node("^", vector<node>{*$1, *$3});
                                }
    | ABS '(' expr ')'          {
                                    $$ = new node("abs", vector<node>{*$3});
                                }
    | SQRT '(' expr ')'         {
                                    $$ = new node("^", vector<node>{*$3, node("0.5")});
                                }
    | EXP '(' expr ')'          {
                                    $$ = new node("exp", vector<node>{*$3});
                                }
    | LOG '(' expr ')'          {
                                    $$ = new node("log", vector<node>{*$3});
                                }
    | SIN '(' expr ')'          {
                                    $$ = new node("sin", vector<node>{*$3});
                                }
    | COS '(' expr ')'          {
                                    $$ = new node("cos", vector<node>{*$3});
                                }
    | TAN '(' expr ')'          {
                                    $$ = new node("tan", vector<node>{*$3});
                                }
    | ASIN '(' expr ')'         {
                                    $$ = new node("asin", vector<node>{*$3});
                                }
    | ACOS '(' expr ')'         {
                                    $$ = new node("acos", vector<node>{*$3});
                                }
    | ATAN '(' expr ')'         {
                                    $$ = new node("atan", vector<node>{*$3});
                                }
    | '(' expr ')'              {
                                    $$ = $2;
                                }
    ;

arthm_expr:
    number                      {
                                    $$ = new node($1);
                                }
    | MINUS arthm_expr %prec UMINUS {
                                        $$ = new node("-", vector<node>{*$2});
                                    }
    | PLUS arthm_expr %prec UPLUS   {
                                        $$ = $2;
                                    }
    | arthm_expr MINUS arthm_expr   {
                                        $$ = new node("-", vector<node>{*$1, *$3});
                                    }
    | arthm_expr PLUS arthm_expr    {
                                        $$ = new node("+", vector<node>{*$1, *$3});
                                    }
    | arthm_expr TIMES arthm_expr   {
                                        $$ = new node("*", vector<node>{*$1, *$3});
                                    }
    | arthm_expr DIVIDE arthm_expr  {
                                        $$ = new node("/", vector<node>{*$1, *$3});
                                    }
    | arthm_expr POWER arthm_expr   {
                                        $$ = new node("^", vector<node>{*$1, *$3});
                                    }
    | ABS '(' arthm_expr ')'    {
                                    $$ = new node("abs", vector<node>{*$3});
                                }
    | SQRT '(' arthm_expr ')'   {
                                    $$ = new node("^", vector<node>{*$3, node("0.5")});
                                }
    | EXP '(' arthm_expr ')'    {
                                    $$ = new node("exp", vector<node>{*$3});
                                }
    | LOG '(' arthm_expr ')'    {
                                    $$ = new node("log", vector<node>{*$3});
                                }
    | SIN '(' arthm_expr ')'    {
                                    $$ = new node("sin", vector<node>{*$3});
                                }
    | COS '(' arthm_expr ')'    {
                                    $$ = new node("cos", vector<node>{*$3});
                                }
    | TAN '(' arthm_expr ')'    {
                                    $$ = new node("tan", vector<node>{*$3});
                                }
    | ASIN '(' arthm_expr ')'   {
                                    $$ = new node("asin", vector<node>{*$3});
                                }
    | ACOS '(' arthm_expr ')'   {
                                    $$ = new node("acos", vector<node>{*$3});
                                }
    | ATAN '(' arthm_expr ')'   {
                                    $$ = new node("atan", vector<node>{*$3});
                                }
    | '(' arthm_expr ')'        {
                                    $$ = $2;
                                }
    ;

reset_props:
	'(' AND reset_prop_list ')'  {
	                                $$ = $3;
	                             }
	;

reset_prop:
    reset_var EQ expr   {
                           $$ = new pair<string, node>($1, *$3);
                        }
    | '(' reset_prop ')' {
                            $$ = $2;
                         }
    ;

reset_prop_list:
    reset_prop_list reset_prop  {
                                    $$->insert(*$2);
                                }
    | reset_prop    {
                        $$ = new map<string, node>();
                        $$->insert(*$1);
                    }
    ;

reset_var:
    identifier PRIME 	{
                            if(pdrh_model.var_exists($1))
                            {
                                $$ = $1;
                            }
                            else
                            {
                                stringstream s;
                                s << "undefined variable \"" << $1 << "\"";
                                yyerror(s.str().c_str());
                            }
						}
	;

reset_state:
	'@' number reset_props ';'  {
	 	                            $$ = new pair<int, map<string, node>>(atoi($2), *$3);
	 	                        }

jumps_section:
	JUMP ':' jumps  {
	                    $$ = $3;
	                }
	| JUMP ':'  {
	                $$ = new vector<jump>();
	            }

jumps:
	jumps jump  {
	                $$->push_back(*$2);
	            }
	| jump  {
	            $$ = new vector<jump>();
	            $$->push_back(*$1);
	        }

jump:
	prop TRANS reset_state  {
	                            $$ = new jump($3->first, *$1, $3->second);
	                        }

init:
	INIT ':' states     {
	                        for(pair<int, node> s : *$3)
	                        {
	                            pdrh_model.push_init(s.first, s.second);
	                        }
	                    }

goal:
	GOAL ':' states     {
	                        for(pair<int, node> s : *$3)
                            {
                                pdrh_model.push_goal(s.first, s.second);
                            }
                        }

state:
	'@' number prop ';' {
	                        $$ = new pair<int, node>(atoi($2), *$3);
	                    }

states:
	states state    {
	                    $$->push_back(*$2);
	                }
	| state {
	            $$ = new vector<pair<int, node>>();
	            $$->push_back(*$1);
	        }
	;

synthesize:
	SYNTHESIZE ':' syn_pairs { ; }

syn_pairs:
	syn_pairs syn_pair ';' { ; }
	| syn_pair ';' { ; }

syn_pair:
    identifier ':' arthm_expr   {
                                /*
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
                                */
                            }

%%

void yyerror(const char *s)
{
	std::cerr << "line " << line_num << ": " << s << std::endl;
	exit(EXIT_FAILURE);
}

model parse_pdrh(string filename)
{
    FILE *pdrhfile = fopen(filename.c_str(), "r");
    if (!pdrhfile)
    {
        stringstream s;
        s << "couldn't open file " << filename;
        throw invalid_argument(s.str());
    }
    stringstream s, pdrhnameprep;
    pdrhnameprep << filename << ".preprocessed";
    // calling c preprocessor
    s << "cpp -w -P " << filename << " > " << pdrhnameprep.str().c_str();
    int res = system(s.str().c_str());
    // cheking the result of system call
    if(res != 0)
    {
        stringstream s;
        s << "problem occured while preprocessing " << filename;
        throw runtime_error(s.str());
    }
    // parsing the preprocessed file
    FILE *pdrhfileprep = fopen(pdrhnameprep.str().c_str(), "r");
    // make sure it's valid:
    if (!pdrhfileprep)
    {
        stringstream s;
        s << "couldn't open " << pdrhnameprep.str();
        throw invalid_argument(s.str());
    }
    // set lex to read from it instead of defaulting to STDIN:
    yyin = pdrhfileprep;
    // parse through the input until there is no more:
    do
    {
        yyparse();
    }
    while (!feof(yyin));
    remove(pdrhnameprep.str().c_str());

    return pdrh_model;
}
