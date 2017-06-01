/********************************************************************************
*
* File: pcat.lex
* The PCAT scanner
*
Omkar Deshmukh
UTA ID: 1001275806
********************************************************************************/

package edu.uta.pcat;

import java_cup.runtime.Symbol;

%%
%class PcatLex
%public
%line
%column
%cup
%state comment


%{

  private Symbol symbol ( int type ) {
    return new Symbol(type, yyline, yycolumn);
  }

  private Symbol symbol ( int type, Object value ) {
    return new Symbol(type, yyline, yycolumn, value);
  }

  public void lexical_error ( String message ) {
    throw new Error("*** Lexical Error: " + message + " (line: " + yyline
                    + ", position: " + yycolumn + ")");
  }
%}

DIGIT=[0-9]
ID=[a-zA-Z][a-zA-Z0-9_]*
	
%%
//Comments
//works well with any type of singleline comments but bad with multiline comments (not in use)
//"(*".*"*)"   	{ /* ignore comments. */ }	

//works well with multiline comments as long as they dont have * in	them (in use)
"(*"[^*]*"*)"	{ /* ignore comments. */ }

//Numbers
{DIGIT}+                { return symbol(sym.INTEGER_LITERAL,new Integer(yytext())); }
{DIGIT}+"."{DIGIT}+     { return symbol(sym.REAL_LITERAL,new Float(yytext())); }

//Keywords
"PROGRAM"		{ return symbol(sym.PROGRAM); }
"IS"			{ return symbol(sym.IS); }
"BEGIN"         { return symbol(sym.BEGIN); }
"END"			{ return symbol(sym.END); }
"EXIT"			{ return symbol(sym.EXIT); }
"READ"			{ return symbol(sym.READ); }
"WRITE"			{ return symbol(sym.WRITE); }
"TO"			{ return symbol(sym.TO); }
"TYPE"			{ return symbol(sym.TYPE); }
"ARRAY"			{ return symbol(sym.ARRAY); }
"IF"			{ return symbol(sym.IF); }
"THEN"			{ return symbol(sym.THEN); }
"ELSE"			{ return symbol(sym.ELSE); }
"ELSIF"			{ return symbol(sym.ELSIF); }
"FOR"			{ return symbol(sym.FOR); }
"DO"			{ return symbol(sym.DO); }
"WHILE"			{ return symbol(sym.WHILE); }
"AND"			{ return symbol(sym.AND); }
"OR"			{ return symbol(sym.OR); }
"NOT"			{ return symbol(sym.NOT); }
"LOOP"			{ return symbol(sym.LOOP); }
"RETURN"		{ return symbol(sym.RETURN); }
"PROCEDURE"		{ return symbol(sym.PROCEDURE); }
"RECORD"		{ return symbol(sym.RECORD); }
"OF"			{ return symbol(sym.OF); }
"VAR"			{ return symbol(sym.VAR); }
"BY"			{ return symbol(sym.BY); }
"DIV"			{ return symbol(sym.DIV); }
"MOD"           { return symbol(sym.MOD); }

//Operators and Delimiters
":="            { return symbol(sym.ASGN); }
"<="            { return symbol(sym.LEQ); }
"<>"            { return symbol(sym.NEQ); }
">="            { return symbol(sym.GEQ); }
"="             { return symbol(sym.EQ); }
"<"             { return symbol(sym.LT); }
">"             { return symbol(sym.GT); }
"."             { return symbol(sym.DOT); }
","             { return symbol(sym.COMMA); }
":"             { return symbol(sym.COLON); }
";"             { return symbol(sym.SEMI); }
"("             { return symbol(sym.LPAREN); }
")"             { return symbol(sym.RPAREN); }
"["             { return symbol(sym.LSQBRA); }
"]"             { return symbol(sym.RSQBRA); }
"{"             { return symbol(sym.LCUBRA); }
"}"             { return symbol(sym.RCUBRA); }
"+"             { return symbol(sym.PLUS); }
"-"             { return symbol(sym.MINUS); }
"*"             { return symbol(sym.TIMES); }
"/"             { return symbol(sym.SLASH); }

//Variables
{ID}            { return symbol(sym.ID,yytext()); }

//Strings
\"[^\"]*\"      { return symbol(sym.STRING_LITERAL,yytext().substring(1,yytext().length()-1)); }

//White Spaces
[ \t\r\n\f]     { /* ignore white spaces. */ }

//Any other invalid characters
.               { lexical_error("Illegal character"); }
