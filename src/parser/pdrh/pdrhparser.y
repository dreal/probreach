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
%token MODEL TIME DIST
%token MODE INVT FLOW JUMP INIT GOAL SYNTHESIZE
%token D_DT IMPLY
%token <sval> model_type
%token <sval> dist_type
%token <sval> elem_fun
%token <sval> identifier
%token <fval> n_float
%token <ival> n_int

%%
pdrh:
	model time declarations

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

var_declaration:
	'[' number ',' number ']' identifier ';' { ; }

const_declaration:
	'[' number ']' identifier ';' { ; }

modes:
	modes mode { ; }
	| mode { ; }

mode:
	'{' MODE '@' n_int ';' invt flow jumps_section '}' { ; }
	| '{' MODE '@' n_int ';' flow jumps_section '}' { ; }

invt:
	INVT ':' props { ; }

props:
	props prop { ; }
	| prop ';' { ; }

// PROPOSITION
prop:

flow:
	FLOW ':' odes { ; }

odes:
	odes ode { ; }
	| ode { ; }

ode:
	D_DT '[' identifier ']' '=' expr ';'

// EXPRESSION
expr:

jumps_section:
	JUMP ':' jumps { ; }

jumps:
	jumps jump { ; }
	| jump { ; }

jump:
	prop IMPLY '@' prop ';' { ; }

init:
	'@' n_int prop ';' { ; }

goal:
	'@' n_int prop ';' { ; }

number:
	n_float { ; }
	| n_int { ; }

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
