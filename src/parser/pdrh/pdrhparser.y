%{
#include <cstdio>
#include <iostream>
#include <string>
#include <sstream>
#include <cmath>
#include <limits>

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
	char *sval;
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

%type<sval> variable
%type<fval> number arthm_expr pdf_bound

%%
pdrh:
	declarations modes init synthesize { ; }
	| declarations modes init goal { ; }
	| model declarations modes init goal { ; }

model:
	MODEL ':' model_type ';'

declarations:
	declarations declaration { ; }
	| declaration { ; }

declaration:
	var_declaration { ; }
	| dist_declaration { ; }

var_declaration:
	'[' arthm_expr ',' arthm_expr ']' identifier ';' { ; }
	| '[' arthm_expr ']' identifier ';'	{ ; }
	| '[' arthm_expr ',' arthm_expr ']' TIME ';' { ; }

dist_declaration:
    PDF '(' expr ',' pdf_bound ',' pdf_bound ',' arthm_expr ')' identifier ';' { ; }
    | G_DIST '(' arthm_expr ',' arthm_expr ')' identifier ';' { ; }
    | N_DIST '(' arthm_expr ',' arthm_expr ')' identifier ';' { ; }
    | U_DIST '(' arthm_expr ',' arthm_expr ')' identifier ';' { ; }
    | E_DIST '(' arthm_expr ')' identifier ';' { ; }
    | DD_DIST '(' dd_pairs ')' identifier ';' { ; }

pdf_bound:
    arthm_expr 		{ $$ = $1; }
    | INFTY 		{ $$ = std::numeric_limits<double>::infinity(); }
    | MINUS INFTY 	{ $$ = -std::numeric_limits<double>::infinity(); }

dd_pairs:
    dd_pairs ',' dd_pair { ; }
    | dd_pair { ; }

dd_pair:
    arthm_expr ':' arthm_expr { ; }

modes:
	modes mode { ; }
	| mode { ; }

mode:
	'{' MODE n_int ';' invt flow jumps_section '}' { ; }
	| '{' MODE n_int ';' flow jumps_section '}' { ; }
	| '{' MODE n_int ';' timeprec flow jumps_section '}' { ; }
	| '{' MODE n_int ';' timeprec invt flow jumps_section '}' { ; }

timeprec:
	TIME_PREC ':' number ';' { ; }

invt:
	INVT ':' prop_list { ; }
	| INVT ':'

prop_list:
	prop_list prop ';' { ; }
	| prop ';' { ; }

props:
	props prop { ; }
	| prop { ; }

prop:
    expr EQ expr { ; }
    | expr GT expr { ; }
    | expr LT expr { ; }
    | expr GE expr { ; }
    | expr LE expr { ; }
    | expr NE expr { ; }
    | TRUE { ; }
    | FALSE { ; }
    | '(' prop ')' { ; }
    | NOT prop { ; }
    | '(' AND props ')' { ; }
    | '(' OR props ')' { ; }
    | '(' XOR props ')' { ; }
    | '(' IMPLY prop prop ')' { ; }

flow:
	FLOW ':' odes { ; }

odes:
	odes ode { ; }
	| ode { ; }

ode:
	D_DT '[' identifier ']' EQ expr ';' { ; }

// SEPARATE A RESET EXPRESSION FROM REGULAR MATHS EXPRESSIONS
expr:
    variable { ; }
    | number { ; }
    | MINUS expr %prec UMINUS { ; }
    | PLUS expr %prec UPLUS { ; }
    | expr PLUS expr { ; }
    | expr MINUS expr { ; }
    | expr TIMES expr { ; }
    | expr DIVIDE expr { ; }
    | expr POWER expr { ; }
    | ABS '(' expr ')' { ; }
    | SQRT '(' expr ')' { ; }
    | EXP '(' expr ')' { ; }
    | LOG '(' expr ')' { ; }
    | SIN '(' expr ')' { ; }
    | COS '(' expr ')' { ; }
    | TAN '(' expr ')' { ; }
    | ASIN '(' expr ')' { ; }
    | ACOS '(' expr ')' { ; }
    | ATAN '(' expr ')' { ; }
    | '(' expr ')' { ; }
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


jumps_section:
	JUMP ':' jumps { ; }
	| JUMP ':' { ; }

jumps:
	jumps jump { ; }
	| jump { ; }

jump:
	prop TRANS state { ; }

init:
	INIT ':' states

goal:
	GOAL ':' states

state:
	'@' n_int prop ';' { ; }

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
    identifier ':' number { ; }

number:
	n_float 			{ $$ = $1 ; }
	| n_int 			{ $$ = $1 ; }

variable:
	identifier 			{ $$ = $1; }
	| identifier PRIME 	{
							std::stringstream s;
							s << $1 << "'";
							$$ = const_cast<char*>(s.str().c_str());
						}
	;

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
}

void yyerror(const char *s) {
	std::cout << " | parse error on line " << line_num << "!  Message: " << s << " --- FAIL" << std::endl;
	// might as well halt now:
	exit(-1);
}
