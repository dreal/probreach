%{
#include <cstdio>
#include <iostream>
#include <string>
#include <sstream>

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
%token MODEL TIME DEFINE
%token DIST PDF N_DIST U_DIST E_DIST G_DIST DD_DIST
%token INFTY
%token WSPACE ENDL

%token MODE INVT FLOW JUMP INIT GOAL SYNTHESIZE
%token D_DT TRANS PRIME

%token EXP LOG SIN COS TAN ASIN ACOS ATAN
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
%left NEG
%right POWER

%%
pdrh:
	declarations modes init goal { ; }
	| declarations modes init synthesize { ; }

declarations:
	declarations declaration { ; }
	| declaration { ; }

declaration:
	var_declaration { ; }
	| dist_declaration { ; }

var_declaration:
	'[' number ',' number ']' identifier ';' { ; }
	| '[' number ']' identifier ';' { ; }
	| '[' number ',' number ']' TIME ';' { ; }

dist_declaration:
    PDF '(' expr ',' pdf_bound ',' pdf_bound ',' number ')' identifier ';' { ; }
    | N_DIST '(' number ',' number ')' identifier ';' { ; }
    | U_DIST '(' number ',' number ')' identifier ';' { ; }
    | E_DIST '(' number ')' identifier ';' { ; }
    | DD_DIST '(' dd_pairs ')' identifier ';' { ; }

pdf_bound:
    number { ; }
    | INFTY { ; }
    | MINUS INFTY { ; }

dd_pairs:
    dd_pairs ',' dd_pair { ; }
    | dd_pair { ; }

dd_pair:
    number ':' number

modes:
	modes mode { ; }
	| mode { ; }

mode:
	'{' MODE n_int ';' invt flow jumps_section '}' { ; }
	| '{' MODE n_int ';' flow jumps_section '}' { ; }

invt:
	INVT ':' props { ; }
	| INVT ':'

props:
	props prop ';' { ; }
	| prop ';' { ; }

prop:
    atom { ; }
    | NOT atom { ; }
    | '(' AND atoms ')' { ; }
    | '(' OR atoms ')' { ; }
    | '(' XOR atoms ')' { ; }
    | '(' IMPLY atom atom ')' { ; }

atoms:
	atoms atom { ; }
	| atom { ; }

atom:
    expr EQ expr { ; }
    | expr GT expr { ; }
    | expr LT expr { ; }
    | expr GE expr { ; }
    | expr LE expr { ; }
    | TRUE { ; }
    | FALSE { ; }
    | '(' atom ')' { ; }
    | NOT atom { ; }
    | '(' AND atoms ')' { ; }
    | '(' OR atoms ')' { ; }
    | '(' XOR atoms ')' { ; }
    | '(' IMPLY atom atom ')' { ; }

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
    | MINUS expr %prec NEG
    | expr PLUS expr { ; }
    | expr MINUS expr { ; }
    | expr TIMES expr { ; }
    | expr DIVIDE expr { ; }
    | expr POWER expr { ; }
    | EXP '(' expr ')' { ; }
    | LOG '(' expr ')' { ; }
    | SIN '(' expr ')' { ; }
    | COS '(' expr ')' { ; }
    | TAN '(' expr ')' { ; }
    | ASIN '(' expr ')' { ; }
    | ACOS '(' expr ')' { ; }
    | ATAN '(' expr ')' { ; }
    | '(' expr ')' { ; }

jumps_section:
	JUMP ':' jumps { ; }

jumps:
	jumps jump { ; }
	| jump { ; }

jump:
	prop TRANS '@' n_int prop ';' { ; }

init:
	INIT ':' '@' n_int prop ';' { ; }

goal:
	GOAL ':' '@' n_int prop ';' { ; }

synthesize:
	SYNTHESIZE ':' syn_pairs { ; }

syn_pairs:
	syn_pairs syn_pair ';' { ; }
	| syn_pair ';' { ; }

syn_pair:
    identifier ':' number

number:
	n_float { ; }
	| n_int { ; }

variable:
	identifier { ; }
	| identifier PRIME { ; }

%%

int main(int argc, char* argv[]) {

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
	std::cout << "File " << argv[1] << " is parsed successfully" << std::endl;
}

void yyerror(const char *s) {
	std::cout << "EEK, parse error on line " << line_num << "!  Message: " << s << std::endl;
	// might as well halt now:
	exit(-1);
}
