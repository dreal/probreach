%{
#include <cstdio>
#include <iostream>

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
%token DIST PDF N_DIST U_DIST E_DIST G_DIST DD_DIST
%token INFTY

%token MODE INVT FLOW JUMP INIT GOAL SYNTHESIZE
%token D_DT TRANS PRIME

%token EXP LOG SIN COS TAN ASIN ACOS ATAN
%token NOT AND OR XOR IMPLY
%token PLUS MINUS TIMES DIVIDE POWER
%token EQ GT LT GE LE
%token TRUE FALSE

%token <sval> model_type
%token <sval> identifier
%token <fval> n_float
%token <ival> n_int

%left PLUS MINUS
%left TIMES DIVIDE
%left NEG
%right POWER

%%
pdrh:
	model time declarations modes init goal { ; }
	| model time declarations modes init synthesize { ; }


model:
	MODEL ':' model_type ';' { ; }

time:
	TIME ':' '[' number ',' number ']' ';' { ; }

declarations:
	declarations declaration { ; }
	| declaration { ; }

declaration:
	var_declaration { ; }
	| const_declaration { ; }
	| dist_declaration { ; }

var_declaration:
	'[' number ',' number ']' identifier ';' { ; }

const_declaration:
	'[' number ']' identifier ';' { ; }

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
	'{' MODE '@' n_int ';' invt flow jumps_section '}' { ; }
	| '{' MODE '@' n_int ';' flow jumps_section '}' { ; }

invt:
	INVT ':' props { ; }

props:
	props prop ';' { ; }
	| prop ';' { ; }

prop:
    atom { ; }
    | NOT atom { ; }
    | atom AND atom { ; }
    | atom OR atom { ; }
    | atom XOR atom { ; }
    | atom IMPLY atom { ; }

atom:
    '(' expr EQ expr ')' { ; }
    | '(' expr GT expr ')' { ; }
    | '(' expr LT expr ')' { ; }
    | '(' expr GE expr ')' { ; }
    | '(' expr LE expr ')' { ; }
    | '(' TRUE ')' { ; }
    | '(' FALSE ')' { ; }

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
	FILE *myfile = fopen(argv[1], "r");
	// make sure it's valid:
	if (!myfile) {
		std::cout << "I can't open " << argv[1] << std::endl;
		return -1;
	}
	// set lex to read from it instead of defaulting to STDIN:
	yyin = myfile;

	// parse through the input until there is no more:
	do {
		yyparse();
	} while (!feof(yyin));

}

void yyerror(const char *s) {
	std::cout << "EEK, parse error on line " << line_num << "!  Message: " << s << std::endl;
	// might as well halt now:
	exit(-1);
}
