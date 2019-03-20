%{
#include <iostream>
#define YY_DECL extern "C" int yylex()
#include "node.h"
#include "model.h"
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

"#define"               { return DEFINE; }

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
"!="                    { return NE; }

"'"                     { return PRIME; }

true                    { return TRUE; }
false                   { return FALSE; }

timeprecision           { return TIME_PREC; }
model                   { return MODEL; }
ha                      { yylval.sval = strdup(yytext); return m_type; }
pha                     { yylval.sval = strdup(yytext); return m_type; }
nha                     { yylval.sval = strdup(yytext); return m_type; }
npha                    { yylval.sval = strdup(yytext); return m_type; }
psy                     { yylval.sval = strdup(yytext); return m_type; }

time                    { return TIME; }

dist_pdf                { return PDF; }
dist_uniform            { return U_DIST; }
dist_normal             { return N_DIST; }
dist_exp                { return E_DIST; }
dist_gamma              { return G_DIST; }
dist_discrete           { return DD_DIST; }
infty                   { return INFTY; }

mode                    { return MODE; }
invt                    { return INVT; }
flow                    { return FLOW; }
"d/dt"                  { return D_DT; }
jump                    { return JUMP; }
init                    { return INIT; }
goal                    { return GOAL; }
sample                  { return SAMPLE; }
paths                   { return PATHS; }
synthesize              { return SYNTHESIZE; }

not	            		{ return NOT; }
and                    	{ return AND; }
or                    	{ return OR; }
xor                    	{ return XOR; }
"=>"                   	{ return IMPLY; }

abs                     { return ABS; }
sqrt              	    { return SQRT; }
exp              	    { return EXP; }
log              	    { return LOGN; }
sin              	    { return SIN; }
cos              	    { return COS; }
tan              	    { return TAN; }
asin              	    { return ASIN; }
acos              	    { return ACOS; }
atan              	    { return ATAN; }

[0-9]+          	                { yylval.sval = strdup(yytext); return number; }
[0-9]*\.?[0-9]+([eE][-+]?[0-9]+)?	{ yylval.sval = strdup(yytext); return number; }
[a-zA-Z_][a-zA-Z0-9_]*              { yylval.sval = strdup(yytext); return identifier; }

[\[\]\(\):;,\{\}@]	    { return yytext[0]; }
"==>"	                { return TRANS; }

\n                      { ++line_num; }
[ \t]+				    ;

%%