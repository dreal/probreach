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

"+"                     { return PLUS; }
"-"                     { return MINUS; }
"*"                     { return TIMES; }
"/"                     { return DIVIDE; }
"^"                     { return POWER; }

"="                     { return EQ; }
">"                     { return GT; }
"<"                     { return LT; }
">="                    { return GE; }
"<="                    { return LE; }

"'"                     { return PRIME; }

TRUE                    { return TRUE; }
FALSE                   { return FALSE; }

model                   { return MODEL; }
ha                      { yylval.sval = strdup(yytext); return model_type; }
pha                     { yylval.sval = strdup(yytext); return model_type; }
nha                     { yylval.sval = strdup(yytext); return model_type; }
npha                    { yylval.sval = strdup(yytext); return model_type; }
psy                     { yylval.sval = strdup(yytext); return model_type; }

time                    { return TIME; }

dist                    { return DIST; }
pdf                     { return PDF; }
u                       { return U_DIST; }
n                       { return N_DIST; }
e                       { return E_DIST; }
g                       { return G_DIST; }
dd                      { return DD_DIST; }
inf                     { return INF; }

mode                    { return MODE; }
invt                    { return INVT; }
flow                    { return FLOW; }
"d/dt"                  { return D_DT; }
jump                    { return JUMP; }
init                    { return INIT; }
goal                    { return GOAL; }
synthesize              { return SYNTHESIZE; }

not	            		{ return NOT; }
and                    	{ return AND; }
or                    	{ return OR; }
xor                    	{ return XOR; }
"=>"                   	{ return IMPLY; }

exp              	    { return EXP; }
log              	    { return LOG; }
sin              	    { return SIN; }
cos              	    { return COS; }
tan              	    { return TAN; }
asin              	    { return ASIN; }
acos              	    { return ACOS; }
atan              	    { return ATAN; }

[0-9]+          	    { yylval.ival = atoi(yytext); return n_int; }

[-+]?[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?	{ yylval.fval = atof(yytext); return n_float; }
[a-zA-Z_][a-zA-Z0-9_]*  { yylval.sval = strdup(yytext); return identifier; }

[\[\]\(\):;,\{\}@]	    { return yytext[0]; }
"==>"	                { return TRANS; }

\n                      { ++line_num; }
.					    ;
%%