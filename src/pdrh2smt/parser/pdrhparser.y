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
	int                         ival;
	float                       fval;
	char*                       sval;
    node*                       nval;
    vector<node*>*              nval_list;
    //mode*                       mode_val;
    //jump*                       jump_val;
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
%type<nval_list> props
%type<nval> pdf_expr prop expr arthm_expr pdf_bound

// to compile
//bison -d -o pdrhparser.c pdrhparser.y && flex -o pdrhlexer.c pdrhlexer.l && g++ -O2 -std=c++11 `/home/fedor/dreal3/build/release/bin/capd-config --cflags` pdrhparser.h pdrhparser.c pdrhlexer.c ../../model.cpp -lfl `/home/fedor/dreal3/build/release/bin/capd-config --libs` -o pdrh && ./pdrh ../../test/parser/test1.pdrh

// declaring some variables
%{
//pdrh::mode *cur_mode = new pdrh::mode;
//pdrh::mode::jump *cur_jump = new pdrh::mode::jump;
//std::vector<pdrh::state> cur_states;
//std::map<pdrh::node*, pdrh::node*> cur_dd;
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
	declarations declaration { ; }
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
	modes mode  { ; }
	| mode      { ; }

mode:
	'{' MODE number ';' invt flow jumps_section '}'              {
	                                                                /*
	                                                                if(pdrh::get_mode(atoi($3)) == NULL)
	                                                                {
                                                                        cur_dd.clear();
                                                                        cur_mode->id = atoi($3);
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
                                                                    */
                                                                }
	| '{' MODE number ';' flow jumps_section '}'                {
	                                                                /*
	                                                                if(pdrh::get_mode(atoi($3)) == NULL)
                                                                    {
                                                                        cur_dd.clear();
                                                                        cur_mode->id = atoi($3);
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
                                                                    */
                                                                }
	| '{' MODE number ';' timeprec flow jumps_section '}'       {
	                                                                /*
	                                                                if(pdrh::get_mode(atoi($3)) == NULL)
                                                                    {
                                                                        cur_dd.clear();
                                                                        cur_mode->id = atoi($3);
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
                                                                    */
                                                                }
	| '{' MODE number ';' timeprec invt flow jumps_section '}'  {
	                                                                /*
	                                                                if(pdrh::get_mode(atoi($3)) == NULL)
                                                                    {
                                                                        cur_dd.clear();
                                                                        cur_mode->id = atoi($3);
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
                                                                    */
                                                                }

timeprec:
	TIME_PREC ':' number ';' { ; }

invt:
	INVT ':' prop_list { ; }
	| INVT ':'

prop_list:
	prop_list prop ';'  {
	                        //pdrh::push_invt(*cur_mode, $2);
                        }
	| prop ';'          {
	                        //pdrh::push_invt(*cur_mode, $1);
	                    }
props:
	props prop              {
	                            $$->push_back($2);
	                        }
	| prop                  {
	                            $$ = new vector<node*>;
	                            $$->push_back($1);
	                        }

prop:
    expr EQ expr            {

                            }
    | expr GT expr          {

                            }
    | expr LT expr          {

                            }
    | expr GE expr          {

                            }
    | expr LE expr          {

                            }
    | expr NE expr          {

                            }
    | TRUE                  {

                            }
    | FALSE                 {

                            }
    | '(' prop ')'          {
                                $$ = $2;
                            }
    | NOT prop              {

                            }
    | '(' AND props ')'     {

                            }
    | '(' OR props ')'      {

                            }
    | '(' XOR props ')'     {

                            }
    | '(' IMPLY prop prop ')'   {

                                }

flow:
	FLOW ':' odes { ; }

odes:
	odes ode { ; }
	| ode { ; }

ode:
	D_DT '[' identifier ']' EQ expr ';'     {
	                                            //pdrh::push_ode(*cur_mode, strdup($3), $6);
	                                            //free($3);
	                                        }

expr:
    identifier                  {
                                    /*
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
                                    */
                                }
    | number                    {
                                    //$$ = pdrh::push_terminal_node($1);
                                }
    | MINUS expr %prec UMINUS   {

                                }
    | PLUS expr %prec UPLUS     {
                                    $$ = $2;
                                }
    | expr MINUS expr           {

                                }
    | expr PLUS expr            {

                                }
    | expr TIMES expr           {

                                }
    | expr DIVIDE expr          {

                                }
    | expr POWER expr           {

                                }
    | ABS '(' expr ')'          {

                                }
    | SQRT '(' expr ')'         {

                                }
    | EXP '(' expr ')'          {

                                }
    | LOG '(' expr ')'          {

                                }
    | SIN '(' expr ')'          {

                                }
    | COS '(' expr ')'          {

                                }
    | TAN '(' expr ')'          {

                                }
    | ASIN '(' expr ')'         {

                                }
    | ACOS '(' expr ')'         {

                                }
    | ATAN '(' expr ')'         {

                                }
    | '(' expr ')'              {
                                    $$ = $2;
                                }
    ;

arthm_expr:
    number                      {

                                }
    | MINUS arthm_expr %prec UMINUS {

                                    }
    | PLUS arthm_expr %prec UPLUS   {
                                        $$ = $2;
                                    }
    | arthm_expr MINUS arthm_expr   {

                                    }
    | arthm_expr PLUS arthm_expr    {

                                    }
    | arthm_expr TIMES arthm_expr   {

                                    }
    | arthm_expr DIVIDE arthm_expr  {

                                    }
    | arthm_expr POWER arthm_expr   {

                                    }
    | ABS '(' arthm_expr ')'    {

                                }
    | SQRT '(' arthm_expr ')'   {
                                    /*
                                    std::vector<pdrh::node*> operands;
                                    operands.push_back($3);
                                    operands.push_back(pdrh::push_terminal_node("0.5"));
                                    $$ = pdrh::push_operation_node("^", operands);
                                    */
                                }
    | EXP '(' arthm_expr ')'    {

                                }
    | LOG '(' arthm_expr ')'    {

                                }
    | SIN '(' arthm_expr ')'    {

                                }
    | COS '(' arthm_expr ')'    {

                                }
    | TAN '(' arthm_expr ')'    {

                                }
    | ASIN '(' arthm_expr ')'   {

                                }
    | ACOS '(' arthm_expr ')'   {

                                }
    | ATAN '(' arthm_expr ')'   {

                                }
    | '(' arthm_expr ')'        {
                                    $$ = $2;
                                }
    ;

reset_props:
	reset_props reset_prop { ; }
	| reset_prop { ; }

reset_prop:
    reset_var EQ expr { ; }
    | TRUE { ; }
    | FALSE { ; }
    | '(' reset_prop ')' { ; }
    | '(' AND reset_props ')' { ; }

reset_var:
    identifier PRIME 	{
                            /*
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
                            */
						}
	;

reset_state:
	'@' number reset_prop ';'   {
	 	                            //cur_jump->next_id = atoi($2);
	 	                        }

jumps_section:
	JUMP ':' jumps { ; }
	| JUMP ':' { ; }

jumps:
	jumps jump { ; }
	| jump { ; }

jump:
	prop TRANS reset_state  {
	                            /*
	                            cur_jump->guard = $1;
	                            pdrh::push_jump(*cur_mode, *cur_jump);
	                            delete cur_jump;
	                            cur_jump = new pdrh::mode::jump;
	                            */
	                        }

init:
	INIT ':' states     {
	                        /*
	                        delete cur_mode;
                         	delete cur_jump;
	                        pdrh::push_init(cur_states);
	                        cur_states.clear();
	                        */
	                    }

goal:
	GOAL ':' states     {
	                        /*
	                        pdrh::push_goal(cur_states);
                            cur_states.clear();
                            */
                        }

state:
	'@' number prop ';' {
	                        /*
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
	                        */
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
