%{
#include <iostream>
#define YY_DECL extern "C" int yylex()
#include "pdrhparser.h"
int line_num = 1;
%}

%x COMMENT

%%

"//".*\n	 		  	{ ++line_num; }

"/*"            		{ BEGIN(COMMENT); }
<COMMENT>"*/" 			{ BEGIN(INITIAL); }
<COMMENT>\n    			{ ++line_num; }
<COMMENT>.    			;

[ \t]				    ;

model                   { return MODEL; }
ha                      { yylval.sval = strdup(yytext); return model_type; }
pha                     { yylval.sval = strdup(yytext); return model_type; }
nha                     { yylval.sval = strdup(yytext); return model_type; }
npha                    { yylval.sval = strdup(yytext); return model_type; }
psy                     { yylval.sval = strdup(yytext); return model_type; }

time                    { return TIME; }

dist                    { std::cout << "token: " << yytext << std::endl; }
pdf                     { std::cout << "token: " << yytext << std::endl; }
u                       { std::cout << "token: " << yytext << std::endl; }
n                       { std::cout << "token: " << yytext << std::endl; }
e                       { std::cout << "token: " << yytext << std::endl; }
g                       { std::cout << "token: " << yytext << std::endl; }
dd                      { std::cout << "token: " << yytext << std::endl; }
inf                     { std::cout << "token: " << yytext << std::endl; }

mode                    { std::cout << "token: " << yytext << std::endl; }
invt                    { std::cout << "token: " << yytext << std::endl; }
flow                    { std::cout << "token: " << yytext << std::endl; }
"d/dt"                  { return D_DT; }
jump                    { std::cout << "token: " << yytext << std::endl; }
init                    { std::cout << "token: " << yytext << std::endl; }
goal                    { std::cout << "token: " << yytext << std::endl; }
synthesize              { std::cout << "token: " << yytext << std::endl; }

not	            		{ std::cout << "set op: " << yytext[0] << std::endl; }
and                    	{ std::cout << "set op: " << yytext << std::endl; }
or                    	{ std::cout << "set op: " << yytext << std::endl; }
xor                    	{ std::cout << "set op: " << yytext << std::endl; }
=>                    	{ std::cout << "set op: " << yytext << std::endl; }

exp              	    { std::cout << "elem funtion: " << yytext << std::endl; }
log              	    { std::cout << "elem funtion: " << yytext << std::endl; }
sin              	    { std::cout << "elem funtion: " << yytext << std::endl; }
cos              	    { std::cout << "elem funtion: " << yytext << std::endl; }
tan              	    { std::cout << "elem funtion: " << yytext << std::endl; }
asin              	    { std::cout << "elem funtion: " << yytext << std::endl; }
acos              	    { std::cout << "elem funtion: " << yytext << std::endl; }
atan              	    { std::cout << "elem funtion: " << yytext << std::endl; }

[0-9]+          	    { yylval.ival = atoi(yytext); return n_int; }
[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?	{ yylval.fval = atof(yytext); return n_float; }
[a-zA-Z_][a-zA-Z0-9_]*  { yylval.sval = strdup(yytext); return identifier; }

[\[\]\(\):;,\{\}@']	    { return yytext[0]; }
==>	                    { return "IMPLY"; }

[-+*/^=><]	            { std::cout << "operator: " << yytext[0] << std::endl; }
">="                    { std::cout << "operator: " << yytext << std::endl; }
"<="                    { std::cout << "operator: " << yytext << std::endl; }

\n                      { ++line_num; }
.					    ;
%%