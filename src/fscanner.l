%{
/*===========================================================================
 Copyright (c) 1998-2000, The Santa Cruz Operation 
 All rights reserved.
 
 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions are met:

 *Redistributions of source code must retain the above copyright notice,
 this list of conditions and the following disclaimer.

 *Redistributions in binary form must reproduce the above copyright notice,
 this list of conditions and the following disclaimer in the documentation
 and/or other materials provided with the distribution.

 *Neither name of The Santa Cruz Operation nor the names of its contributors
 may be used to endorse or promote products derived from this software
 without specific prior written permission. 

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS ``AS
 IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE
 LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 INTERRUPTION)
 HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
 DAMAGE. 
 =========================================================================*/

/*	cscope - interactive C symbol cross-reference
 *
 *	C symbol scanner
 */
#include "global.h"
#include "alloc.h"
#include "scanner.h"
#include "lookup.h"

#include <assert.h>

/* the line counting has been moved from character reading for speed */
/* comments are discarded */

#ifndef FLEX_SCANNER
# error Sorry, this scanner needs flex. It is not usable with AT&T Lex.
#endif

#define	IFLEVELINC	5	/* #if nesting level size increment */
#define	SCOPEINC	10	/* class/namespace nesting size increment */
#define YY_NO_TOP_STATE 1

int	first;	/* buffer index for first char of symbol */
int	last;	/* buffer index for last char of symbol */
int	lineno;	/* symbol line number */
int	myylineno = 1;

/* HBB 20001007: new variables, emulating yytext in a way that allows 
 * the yymore() simulation, my_yymore(), to be used even in the presence of 
 * yyless(). */
size_t my_yyleng = 0;
char *my_yytext = NULL;

static	BOOL	accesskw;		/* last word was public, private or protected */
static	int	angles;			/* template <> nesting in a base class list */
static	BOOL	arraydimension;		/* inside array dimension declaration */
static	BOOL	bplisting;		/* breakpoint listing */
static	int	braces;			/* unmatched left brace count */
static	BOOL	elseelif;		/* #else or #elif found */
static	BOOL	esudef;			/* enum/struct/union global definition */
static	BOOL	external;		/* external definition */
static	int	externalbraces;		/* external definition outer brace count */
static	BOOL	fcndef;			/* function definition */
static	BOOL	headbases;		/* class/struct head has a base class list */
static	BOOL	inbases;		/* inside a class/struct base class list */
static	BOOL	global;			/* file global scope (outside functions) */
static	size_t	iflevel;		/* #if nesting level */
static	BOOL	initializer;		/* data initializer */
static	int	initializerbraces;	/* data initializer outer brace count */
static	BOOL	lex;			/* lex file */
static	size_t	miflevel = IFLEVELINC;	/* maximum #if nesting level */
static	int	*maxifbraces;		/* maximum brace count within #if */
static	int	*preifbraces;		/* brace count before #if */
static	int	parens;			/* unmatched left parenthesis count */
static	BOOL	ppdefine;		/* preprocessor define statement */
static	BOOL	pseudoelif;		/* pseudo-#elif */
static	BOOL	nspending;		/* "namespace" seen, waiting for its body */
static	BOOL	oldtype;		/* next identifier is an old type */
static	BOOL	prevenum;		/* last word was "enum" */
static	BOOL	qualifier;		/* identifier is followed by :: */
static	BOOL	rules;			/* lex/yacc rules */
static	BOOL	scopepending;		/* class/struct/union body is next */
static	int	*scopebraces;		/* brace count in each class/namespace body */
static	BOOL	*scopeclass;		/* each scope is a class/struct, not a namespace */
static	size_t	nscope;			/* class/namespace nesting level */
static	size_t	mscope = SCOPEINC;	/* maximum class/namespace nesting level */
static	int	scopelevel;		/* brace count in the innermost class or
					   namespace body, 0 at file scope; function
					   definitions begin at this brace count */
static	BOOL	sdl;			/* sdl file */
static	BOOL	structfield;		/* structure field declaration */
static	int	tagdef;			/* class/enum/struct/union tag definition */
static	int	tparams;		/* template <parameter> nesting */
static	BOOL	template;		/* function template */
static	int	templateparens;		/* function template outer parentheses count */
static	int	typedefbraces = -1;	/* initial typedef brace count */
static	int	token;			/* token found */
static	int 	ident_start;		/* begin of preceding identifier */

static	void	my_yymore(void);
static	void	pushscope(BOOL isclass);
static	void	popscopes(void);

%}
identifier	[a-zA-Z_$][a-zA-Z_0-9$]*
number		\.?[0-9][.0-9a-fA-FlLuUxX]*
comment		"/*"([^*]*("*"+[^/])?)*"*/"|"//"[^\n]*\n
ws		[ \t\r\v\f]
wsnl		[ \t\r\v\f\n]|{comment}

/* flex options: stack of start conditions, and don't use yywrap() */
%option stack
%option noyywrap

%start SDL
%a 4000
%o 7000

/* exclusive start conditions. not available in AT&T lex -> use flex! */
%x IN_PREPROC WAS_ENDIF WAS_IDENTIFIER WAS_ESU IN_DQUOTE IN_SQUOTE COMMENT

%%

%\{		{	/* lex/yacc C declarations/definitions */
			global = YES;
			goto more;
			/* NOTREACHED */
		}
%\}		{
			global = NO;
			goto more;
			/* NOTREACHED */
		}
^%%		{	/* lex/yacc rules delimiter */
			braces = 0;
			if (rules == NO) {
				/* this %% starts the section containing the rules */
				rules = YES;

				/* Copy yytext to private buffer, to be able to add further
				 * content following it: */
				my_yymore();

				/* simulate a yylex() or yyparse() definition */
				(void) strcat(my_yytext, " /* ");
				first = strlen(my_yytext);
				if (lex == YES) {
					(void) strcat(my_yytext, "yylex");
				} else {	
					/* yacc: yyparse implicitly calls yylex */
					char *s = " yylex()";
					char *cp = s + strlen(s);
					while (--cp >= s) {
						unput(*cp);
					}
					(void) strcat(my_yytext, "yyparse");
				}
				last = strlen(my_yytext);
				(void) strcat(my_yytext, " */");
				my_yyleng = strlen(my_yytext);
				return(FCNDEF);
			} else {
				/* were in the rules section, now comes the closing one */
				rules = NO;
				global = YES;
				last = first;
				my_yymore();
				return(FCNEND);
				/* NOTREACHED */
			}
		}

<SDL>STATE[ \t]+({identifier}|\*)	{ /* sdl state, treat as function def */
			braces = 1;
			fcndef = YES;
			token = FCNDEF;
			goto findident;
			/* NOTREACHED */
		}
<SDL>ENDSTATE[ \t]	{ /* end of an sdl state, treat as end of a function */
			goto endstate;
			/* NOTREACHED */
		}

\{		{	/* count unmatched left braces for fcn def detection */
			++braces;

			/* the body of a class or namespace is a new scope in
			   which functions can be defined */
			if (scopepending == YES || nspending == YES) {
				pushscope(scopepending);
			}
			scopepending = nspending = NO;
			inbases = headbases = NO;
			angles = 0;

			/* a '{' ends a base class list or constructor
			   initializer list, not a structure field */
			if (cplusplus == YES) {
				structfield = NO;
			}
			
			/* mark an untagged enum/struct/union so its beginning
			   can be found */
			if (tagdef) {
				if (braces == 1) {
					esudef = YES;
				}
				token = tagdef;
				tagdef = '\0';
				last = first;
				my_yymore();
				return(token);
			}
			goto more;
			/* NOTREACHED */
		}

\#{ws}*	{ /* start a preprocessor line */
			if (rules == NO)		/* don't consider CPP for lex/yacc rules */
				BEGIN(IN_PREPROC);
			yyleng = 1;	/* get rid of the blanks, if any */
			goto more;
			/* NOTREACHED */
		}
<IN_PREPROC>endif([^a-zA-Z0-9_$\n].*)?	{	/* #endif */
			/* delay treatment of #endif depending on whether an
			 * #if comes right after it, or not */
			/* HBB 20010619: new pattern allows trailing garbage
			 * after the #endif */
			BEGIN(WAS_ENDIF);
			goto more;
			/* NOTREACHED */
		}
<WAS_ENDIF>\n{wsnl}*#{ws}*if(ndef|def)?{ws}+		{
			/* attempt to correct erroneous brace count caused by:
			 * 
			 * #if ...
			 * 	... {
			 * #endif
			 * #if ...
			 * 	... {
			 * #endif
			 */
			/* the current #if must not have an #else or #elif */
			if (elseelif == YES) {
				goto endif;
				/* NOTREACHED */
			}
			pseudoelif = YES;
			BEGIN(INITIAL);
			yyless(1);	/* rescan all but the line ending */
			yy_set_bol(1);
			goto eol;
			/* NOTREACHED */
		}
<WAS_ENDIF>\n{wsnl}*		 { 	/* an #endif with no #if right after it */
		endif:
			if (iflevel > 0) {
				/* get the maximum brace count for this #if */
				if (braces < maxifbraces[--iflevel]) {
					braces = maxifbraces[iflevel];
				}
			}
			BEGIN(INITIAL);
			yyless(1);
			yy_set_bol(1);
			goto eol;
			/* NOTREACHED */
		}

<IN_PREPROC>ifndef{ws}+	|
<IN_PREPROC>ifdef{ws}+		|
<IN_PREPROC>if{ws}+		{ /* #if directive */
			elseelif = NO;
			if (pseudoelif == YES) {
				pseudoelif = NO;
				goto elif;
				/* NOTREACHED */
			}
			/* make sure there is room for the current brace count */
			if (iflevel == miflevel) {
				miflevel += IFLEVELINC;
				maxifbraces = myrealloc(maxifbraces, miflevel * sizeof(*maxifbraces));
				preifbraces = myrealloc(preifbraces, miflevel * sizeof(*preifbraces));
			}
			/* push the current brace count */
			preifbraces[iflevel] = braces;
			maxifbraces[iflevel++] = 0;
			BEGIN(INITIAL);
			goto more;
			/* NOTREACHED */
		}
<IN_PREPROC>else({ws}.*)?	{ /* #else --- eat up whole line */
			elseelif = YES;
			if (iflevel > 0) {
				
				/* save the maximum brace count for this #if */
				if (braces > maxifbraces[iflevel - 1]) {
					maxifbraces[iflevel - 1] = braces;
				}
				/* restore the brace count to before the #if */
				braces = preifbraces[iflevel - 1];
			}
			BEGIN(INITIAL);
			goto more;
			/* NOTREACHED */
		}
<IN_PREPROC>elif{ws}+	{ /* #elif */
			/* elseelif = YES; --- HBB I doubt this is correct */
		elif:
			if (iflevel > 0) {
				
				/* save the maximum brace count for this #if */
				if (braces > maxifbraces[iflevel - 1]) {
					maxifbraces[iflevel - 1] = braces;
				}
				/* restore the brace count to before the #if */
				braces = preifbraces[iflevel - 1];
			}
			BEGIN(INITIAL);
			goto more;
			/* NOTREACHED */
		}

<IN_PREPROC>include{ws}*\"[^"\n]+\" |
<IN_PREPROC>include{ws}*<[^>\n]+> 	{ /* #include file */
			char	*s;
			char remember = yytext[yyleng-1];
			
			my_yymore();
			s = strpbrk(my_yytext, "\"<");
			if (!s)
				return(LEXERR);
			my_yytext[my_yyleng-1] = '\0';
			incfile(s + 1, s);
			my_yytext[my_yyleng-1] = remember;
			first = s - my_yytext;
			last = my_yyleng - 1;
			if (compress == YES) {
				my_yytext[0] = '\2';	/* compress the keyword */
			}
			BEGIN(INITIAL);
			return(INCLUDE);
			/* NOTREACHED */
		}

\}		{
			/* could be the last enum member initializer */
			if (braces == initializerbraces) {
				initializerbraces = -1;
				initializer = NO;
			}
			if (--braces <= 0) {
		endstate:
				braces = 0;
			}
			popscopes();
			if (braces == scopelevel) {

				/* if the end of the function (a C++ function
				   can be inside a class or struct definition) */
				if (fcndef == YES && (esudef == NO || cplusplus == YES)) {
					fcndef = NO;
					last = first;
					my_yymore();
					return(FCNEND);
				}
				/* if the end of an enum/struct/union definition */
				if (esudef == YES) {
					esudef = NO;
				}
				/* back in the members of an enclosing class */
				if (nscope > 0 && scopeclass[nscope - 1] == YES) {
					esudef = YES;
				}
			}
			goto more;
			/* NOTREACHED */
		}

\(		{	/* count unmatched left parentheses for function templates */
			++parens;
			goto more;
			/* NOTREACHED */
		}
\)		{
			if (--parens <= 0) {
				parens = 0;
			}
			/* if the end of a function template */
			if (parens == templateparens) {
				templateparens = -1;
				template = NO;
			}
			goto more;
			/* NOTREACHED */
		}
=		{	/* if a global definition initializer */
			if (!my_yytext)
				return(LEXERR);
			if (global == YES && ppdefine == NO && my_yytext[0] != '#') {
				initializerbraces = braces;
				initializer = YES;
			}
			goto more;
			/* NOTREACHED */
		}
::		{	/* C++ scope resolution */
			cplusplus = YES;
			goto more;
			/* NOTREACHED */
		}
:		{	/* a if global structure field */
			if (!my_yytext)
				return(LEXERR);
			/* not the end of "public:", "private:" or "protected:" */
			if (global == YES && ppdefine == NO && my_yytext[0] != '#' &&
			    accesskw == NO) {
				structfield = YES;
			}
			accesskw = NO;
			goto more;
			/* NOTREACHED */
		}
\<		{	/* template parameter or base class argument list */
			if (tparams > 0) {
				++tparams;
			} else if (inbases == YES) {
				++angles;
			}
			goto more;
			/* NOTREACHED */
		}
\>		{
			if (tparams > 0) {
				--tparams;
			} else if (inbases == YES && angles > 0) {
				--angles;
			}
			goto more;
			/* NOTREACHED */
		}
\,		{
			if (braces == initializerbraces) {
				initializerbraces = -1;
				initializer = NO;
			}
			structfield = NO;
			goto more;
			/* NOTREACHED */
		}
;		{	/* if the enum/struct/union was not a definition */
			if (braces == 0) {
				esudef = NO;
			}
			/* a C++ function declaration mistaken for a definition */
			if (cplusplus == YES && fcndef == YES && braces == scopelevel) {
				fcndef = NO;
			}
			/* not a class/struct/union or namespace body after all */
			scopepending = nspending = NO;
			inbases = headbases = NO;
			angles = 0;
			/* if the end of a typedef */
			if (braces == typedefbraces) {
				typedefbraces = -1;
			}
			/* if the end of a external definition */
			if (braces == externalbraces) {
				externalbraces = -1;
				external = NO;
			}
			structfield = NO;
			initializer = NO;
			goto more;
			/* NOTREACHED */
		}
<IN_PREPROC>define{ws}+{identifier}	{
				
			/* preprocessor macro or constant definition */
			ppdefine = YES;
			token = DEFINE;
			if (compress == YES) {
				my_yytext[0] = '\1';	/* compress the keyword */
			}
		findident:
			/* search backwards through yytext[] to find the identifier */
			/* NOTE: this had better be left to flex, by use of
			 * yet another starting condition */
			my_yymore();
			first = my_yyleng - 1;
			while (my_yytext[first] != ' ' && my_yytext[first] != '\t') {
				--first;
			}
			++first;
			last = my_yyleng;
			BEGIN(INITIAL);
			goto definition;
			/* NOTREACHED */
		}
<IN_PREPROC>\n	{   /* unknown preprocessor line */
			BEGIN(INITIAL);
                        ++myylineno;
			goto more;
			/* NOTREACHED */
		}
<IN_PREPROC>.		 |
<IN_PREPROC>{identifier}	{   /* unknown preprocessor line */
			BEGIN(INITIAL);
			goto more;
			/* NOTREACHED */
		}

class{wsnl}+{identifier}({wsnl}|{identifier}|[()])*(":"[^;{}]*)?\{	{	/* class definition */
			cplusplus = YES;
			if (prevenum == YES) {		/* enum class */
				tagdef = 'e';
			} else {
				tagdef =  'c';
				scopepending = YES;
				headbases = strchr(yytext, ':') != NULL ? YES : NO;
			}
			prevenum = NO;
			yyless(5);		/* eat up 'class', and re-scan */
			yy_set_bol(0);
			goto more;
			/* NOTREACHED */
		}

("enum"|"struct"|"union")	{
			ident_start = first;
			prevenum = yytext[0] == 'e' ? YES : NO;
			BEGIN(WAS_ESU);
			goto more;
		}
<WAS_ESU>{
({wsnl}+{identifier}){wsnl}*\{		{ /* e/s/u definition */
			tagdef = my_yytext[ident_start];
			if (tagdef != 'e' && cplusplus == YES) {
				scopepending = YES;
			}
			BEGIN(WAS_IDENTIFIER);
			goto ident;
		}
({wsnl}+{identifier}){wsnl}*":"[^;{}]*\{	{ /* e/s/u definition with a base class list */
			tagdef = my_yytext[ident_start];
			if (tagdef != 'e') {
				cplusplus = YES;
				scopepending = YES;
				headbases = YES;
			}
			BEGIN(WAS_IDENTIFIER);
			goto ident;
		}
{wsnl}*\{		{ /* e/s/u definition without a tag */
			tagdef = my_yytext[ident_start];
			BEGIN(INITIAL);
			if (braces == 0) {
				esudef = YES;
			}
			last = first;
			yyless(0);  /* re-scan all this as normal text */
			tagdef = '\0';
			goto more;
		}
({wsnl}+{identifier})?{wsnl}* 	|   
.|\n										{   /* e/s/u usage */
			BEGIN(WAS_IDENTIFIER);
			goto ident;
		}
}

if{wsnl}*\(	{ 	/* ignore 'if' */
			yyless(2);
			yy_set_bol(0);
			goto more;
}	

template{wsnl}*"<"	{	/* C++ template parameter list */
			cplusplus = YES;
			tparams = 1;
			goto more;
			/* NOTREACHED */
		}
namespace/({wsnl}+{identifier}("::"{identifier})*)?{wsnl}*"{"	{	/* C++ namespace body */
			cplusplus = YES;
			nspending = YES;
			goto more;
			/* NOTREACHED */
		}
operator{ws}*("()"|"[]"|[-+*/%^&|~!=<>,]+)	{	/* C++ operator function name */
			BEGIN(WAS_IDENTIFIER);
			ident_start = first;
			goto more;
			/* NOTREACHED */
		}
{identifier}	{	/* identifier found: do nothing, yet. (!) */
			BEGIN(WAS_IDENTIFIER);
			prevenum = NO;
			ident_start = first;
			goto more;
			/* NOTREACHED */
		}

<WAS_IDENTIFIER>{       
{ws}*"::"	|
{ws}*"<"([^;{}()<>]|"<"[^;{}()<>]*">")*">"{ws}*"::"	{
			/* C++ class or namespace name in a qualified name */
			cplusplus = YES;
			qualifier = YES;
			goto ident;
			/* NOTREACHED */
		}
{ws}*"<"([^;{}()<>]|"<"[^;{}()<>]*">")*">"({wsnl}|[*&])*[a-zA-Z_]	{
			/* a C++ template type used in a declaration, as in
			 * "vector<int> v;"; but not in a base class list */
			if (inbases == YES) {
				goto generic;
			}
			goto ident;
			/* NOTREACHED */
		}
{ws}*\(({wsnl}|{identifier}|{number}|[*&[\]=,.:<>])*\)({wsnl}|const|volatile|noexcept|override|final|"&&"|"&")*[;=]	{
			/* a C++ member function declaration, not a definition,
			 * even though it may have "const" etc. after the arguments */
			goto fcncal;
			/* NOTREACHED */
		}
{ws}*\(({wsnl}|{identifier}|{number}|[*&[\]=,.:<>])*\)([()]|{wsnl})*[:a-zA-Z_#{]	{
			/* a function definition */
			/* note: "#define a (b) {" and "#if defined(a)\n#" 
			 * are not fcn definitions! */
			/* warning: "if (...)" must not overflow yytext, 
			 * so the content of function argument definitions 
			 * is restricted, in particular parentheses are 
			 * not allowed */
			/* FIXME HBB 20001003: the above 'not allowed' may well be the
			 * reason for the parsing bug concerning function pointer usage,
			 * I suspect. --- I think my new special-case rule for 'if'
			 * could be helpful in removing that limitation */
			/* note: a C++ constructor's member initializers, as in
			 * "A::A() : b(1) {", are not function definitions */
			if (braces == scopelevel && ppdefine == NO &&
			    my_yytext[0] != '#' && rules == NO &&
			    (fcndef == NO || cplusplus == NO)) {
				fcndef = YES;
				token = FCNDEF;
				goto fcn;
				/* NOTREACHED */
			}
			goto fcncal;
			/* NOTREACHED */
		}
{ws}*\(([*&[\]=,.]|{identifier}|{number}|{wsnl})*		{ 	/* function call */
		fcncal:	if (fcndef == YES || ppdefine == YES || rules == YES) {
				token = FCNCALL;
				goto fcn;
				/* NOTREACHED */
			}
			if (template == NO) {
				templateparens = parens;
				template = YES;
			}
			goto ident;
			/* NOTREACHED */
		}
("*"|{wsnl})+{identifier}		{	/* typedef name or modifier use */
			goto ident;
			/* NOTREACHED */
		}
.|\n	{		/* general identifer usage */
			char	*s;
			BOOL	wasqualifier;

		generic:
			if (global == YES && ppdefine == NO && my_yytext[0] != '#' &&
			    external == NO && initializer == NO && 
			    arraydimension == NO && structfield == NO &&
			    template == NO && fcndef == NO && inbases == NO &&
			    tparams == 0) {
				if (esudef == YES) {	
					/* if enum/struct/union */
					token = MEMBERDEF;
				} else {
					token = GLOBALDEF;
				}
			} else {
		ident:
				token = IDENT;
			}
		fcn:
			if (YYSTATE == WAS_IDENTIFIER) {
				/* Position back to the actual identifier: */
				last = first; 
				first = ident_start;
				yyless(0);
				/* HBB 20001008: if the anti-backup-pattern above matched,
				 * and the matched context ended with a \n, then the scanner
				 * believes it's at the start of a new line. But the yyless()
				 * should feeds that \n back into the input, so that's
				 * wrong. --> force 'beginning-of-line' status off. */
				yy_set_bol(0);
				BEGIN(INITIAL);
			} else {
				my_yymore();
				last = my_yyleng;
			}
		definition:

			/* if a long line */
			if (yyleng > STMTMAX) {
				int	c;
				
				/* skip to the end of the line */
				warning("line too long");
				while ((c = input()) > LEXEOF) { 
					if (c == '\n') {
						unput(c);
						break;
					}
				}
			}
			/* truncate a long symbol */
			if (yyleng > PATLEN) {
				warning("symbol too long");
				my_yyleng = first + PATLEN;
				my_yytext[my_yyleng] = '\0';
			}

			wasqualifier = qualifier;
			qualifier = NO;

			/* if found word was a keyword: */
			if ((s = lookup(my_yytext + first)) != NULL) {
				first = my_yyleng;

				if (cplusplus == YES) {
					if (strcmp(s, "namespace") == 0) {
						nspending = YES;
					}
					accesskw = strcmp(s, "public") == 0 ||
					    strcmp(s, "private") == 0 ||
					    strcmp(s, "protected") == 0 ? YES : NO;
				}
				
				/* if the start of a typedef */
				if (s == typedeftext) {
					typedefbraces = braces;
					oldtype = YES;
				}
				/* if an enum/struct/union */
				/* (needed for "typedef struct tag name;" so
				   tag isn't marked as the typedef name) */
				else if (s == enumtext || s == structtext || s == uniontext) {
					/* do nothing */
				} else if (s == externtext) {
					/* if an external definition */
					externalbraces = braces;
					external = YES;
				} else if (templateparens == parens && template == YES) {
					/* keyword doesn't start a function 
					 * template */
					templateparens = -1;
					template = NO;
				} else {	
					/* identifier after typedef was a 
					 * keyword */
					oldtype = NO;
				}
			} else {	
				/* not a keyword --> found an identifier */
				/* last = yyleng; */
				
				/* if a class/enum/struct/union tag definition */
				/* FIXME HBB 20001001: why reject "class"? */
				if (tagdef && strnotequal(my_yytext + first, "class")) {
					token = tagdef;
					tagdef = '\0';
					if (braces == scopelevel) {
						esudef = YES;
					}
					inbases = headbases;
					angles = 0;
				} else if (tparams > 0) {
					token = IDENT;
				} else if (inbases == YES) {
					/* a base class name, but not a template
					 * argument or a namespace/class qualifier */
					token = (angles == 0 && wasqualifier == NO) ?
					    BASECLASS : IDENT;
				} else if (braces == typedefbraces && oldtype == NO &&
				           arraydimension == NO) {
					/* if a typedef name */
					token = TYPEDEF;
				} else {
					oldtype = NO;
				}
				/* my_yymore(); */
				return(token);
				/* NOTREACHED */
			}
		}
}

\[		{	/* array dimension (don't worry or about subscripts) */
			arraydimension = YES;
			goto more;
			/* NOTREACHED */
		}
\]		{
			arraydimension = NO;
			goto more;
			/* NOTREACHED */
		}
\\\n		{	/* preprocessor statement is continued on next line */
			/* save the '\\' to the output file, but not the '\n': */
			yyleng = 1;
			my_yymore();
			goto eol;
			/* NOTREACHED */
		}
\n		{	/* end of the line */
			if (ppdefine == YES) {	/* end of a #define */
				ppdefine = NO;
				yyless(yyleng - 1);
				last = first;
				my_yymore();
				return(DEFINEEND);
			}
			/* skip the first 8 columns of a breakpoint listing line */
			/* and skip the file path in the page header */
			if (bplisting == YES) {
				int	c, i;

				/* FIXME HBB 20001007: should call input() instead */
				switch (input()) {	/* tab and EOF just fall through */
				case ' ':	/* breakpoint number line */
				case '[':
					for (i = 1; i < 8 && input() > LEXEOF; ++i)
						;
					break;
				case '.':	/* header line */
				case '/':
					/* skip to the end of the line */
					while ((c = input()) > LEXEOF) {
						if (c == '\n') {
							unput(c);
							break;
						}
					}
					break;
				case '\n':	/* empty line */
					unput('\n');
					break;
				}
			}
		eol:
			++myylineno;
			first = 0;
			last = 0;
			if (symbols > 0) {
				/* no my_yymore(): \n doesn't need to be in my_yytext */
				return(NEWLINE);
			}
			/* line ended --> flush my_yytext */
			if (my_yytext)
				*my_yytext = '\0';
			my_yyleng = 0;
			lineno = myylineno;
		}

\'		{	/* character constant */
			if (sdl == NO) 
				BEGIN(IN_SQUOTE);
			goto more;
			/* NOTREACHED */
		}
<IN_SQUOTE>\'	{	
			BEGIN(INITIAL);
			goto more;
			/* NOTREACHED */
		}
\"		{	/* string constant */
			BEGIN(IN_DQUOTE);
			goto more;
			/* NOTREACHED */
		}
<IN_DQUOTE>\"	{	
			BEGIN(INITIAL);
			goto more;
			/* NOTREACHED */
		}
<IN_DQUOTE,IN_SQUOTE>{
\n	  	{	/* syntax error: unexpected EOL */
			BEGIN(INITIAL);
			goto eol;
			/* NOTREACHED */
		}
\\.	|
.		{
			goto more;
			/* NOTREACHED */
		}
\\\n 	{		/* line continuation inside a string! */
			myylineno++;
			goto more;
			/* NOTREACHED */
		}
}
	
^{ws}+		{		/* don't save leading white space */
		}
		
{ws}+\n 	{		/* eat whitespace at end of line */
			unput('\n');
		}

[\t\r\v\f]+	{	/* eat non-blank whitespace sequences, replace
			 * by single blank */
			unput(' ');
		}

{ws}{2,}	{   /* compress sequential whitespace here, not in putcrossref() */
			unput(' ');
 		}

"/*"					yy_push_state(COMMENT);
<COMMENT>{
[^*\n]*			|
"*"+[^*/\n]*	; /* do nothing */
[^*\n]*\n		|
"*"+[^*/\n]*\n	{
			if (ppdefine == NO) {
				goto eol;
			} else {
				++myylineno;
			}
			/* NOTREACHED */
		}
"*"+"/"		{
			/* replace the comment by a single blank */
			unput(' ');
			yy_pop_state();
		}
}		

"//".*\n?		{
			/* C++-style one-line comment */
			goto eol;
			/* NOTREACHED */
		}

{number}				|	/* number */
<SDL>STATE[ \t]+		|   /* ... and other syntax error catchers... */
.						{	/* punctuation and operators */
						more:	
							my_yymore();
							first = my_yyleng;
						}

%%

void
initscanner(char *srcfile)
{
	char	*s;
	
	if (scopebraces == NULL) {
		scopebraces = mymalloc(mscope * sizeof(*scopebraces));
		scopeclass = mymalloc(mscope * sizeof(*scopeclass));
	}
	if (maxifbraces == NULL) {
		maxifbraces = mymalloc(miflevel * sizeof(*maxifbraces));
		preifbraces = mymalloc(miflevel * sizeof(*preifbraces));
	}
	first = 0;		/* buffer index for first char of symbol */
	last = 0;		/* buffer index for last char of symbol */
	lineno = 1;		/* symbol line number */
	myylineno = 1;		/* input line number */
	arraydimension = NO;	/* inside array dimension declaration */
	bplisting = NO;		/* breakpoint listing */
	braces = 0;		/* unmatched left brace count */
	accesskw = NO;		/* last word was public, private or protected */
	angles = 0;		/* template <> nesting in a base class list */
	elseelif = NO;		/* #else or #elif found */
	esudef = NO;		/* enum/struct/union global definition */
	external = NO;		/* external definition */
	externalbraces = -1;	/* external definition outer brace count */
	fcndef = NO;		/* function definition */
	headbases = NO;		/* class/struct head has a base class list */
	inbases = NO;		/* inside a class/struct base class list */
	global = YES;		/* file global scope (outside functions) */
	iflevel = 0;		/* #if nesting level */
	initializer = NO;	/* data initializer */
	initializerbraces = -1;	/* data initializer outer brace count */
	lex = NO;		/* lex file */
	parens = 0;		/* unmatched left parenthesis count */
	ppdefine = NO;		/* preprocessor define statement */
	pseudoelif = NO;	/* pseudo-#elif */
	nspending = NO;		/* "namespace" seen, waiting for its body */
	oldtype = NO;		/* next identifier is an old type */
	prevenum = NO;		/* last word was "enum" */
	qualifier = NO;		/* identifier is followed by :: */
	tparams = 0;		/* template <parameter> nesting */
	rules = NO;		/* lex/yacc rules */
	scopepending = NO;	/* class/struct/union body is next */
	nscope = 0;		/* class/namespace nesting level */
	scopelevel = 0;		/* brace count in innermost class/namespace body */
	sdl = NO;		/* sdl file */
	structfield = NO;	/* structure field declaration */
	tagdef = '\0';		/* class/enum/struct/union tag definition */
	template = NO;		/* function template */
	templateparens = -1;	/* function template outer parentheses count */
	typedefbraces = -1;	/* initial typedef braces count */
	ident_start = 0;	/* start of previously found identifier */

	if (my_yytext)
		*my_yytext = '\0';
	my_yyleng = 0;
	
	BEGIN(INITIAL);

	cplusplus = NO;		/* scanning C++ source */

	/* if this is not a C file */
	if ((s = strrchr(srcfile, '.')) != NULL) {
		switch (*++s) {	/* this switch saves time on C files */
		case 'b':
			if (strcmp(s, "bp") == 0) {	/* breakpoint listing */
				bplisting = YES;
			}
			break;
		case 'l':
			if (strcmp(s, "l") == 0) {	/* lex */
				lex = YES;
				global = NO;
			}
			break;
		case 's':
			if (strcmp(s, "sd") == 0) {	/* sdl */
				sdl = YES;
				BEGIN(SDL);
			}
			break;
		case 'y':
			if (strcmp(s, "y") == 0) {	/* yacc */
				global = NO;
			}
			break;
		case 'c':
		case 'C':
		case 'h':
		case 'H':
		case 'i':
		case 't':
			/* C++ source, header and template files; a header
			 * that is not recognized here is still detected as
			 * C++ once it uses a C++ construct */
			if (strcmp(s, "cc") == 0 || strcmp(s, "cpp") == 0 ||
			    strcmp(s, "cxx") == 0 || strcmp(s, "C") == 0 ||
			    strcmp(s, "hh") == 0 || strcmp(s, "hpp") == 0 ||
			    strcmp(s, "hxx") == 0 || strcmp(s, "H") == 0 ||
			    strcmp(s, "ipp") == 0 || strcmp(s, "inl") == 0 ||
			    strcmp(s, "tcc") == 0 || strcmp(s, "tpp") == 0) {
				cplusplus = YES;
			}
			break;
		}
	}
}

/* enter the body of a class or namespace */
static void
pushscope(BOOL isclass)
{
	if (nscope == mscope) {
		mscope += SCOPEINC;
		scopebraces = myrealloc(scopebraces, mscope * sizeof(*scopebraces));
		scopeclass = myrealloc(scopeclass, mscope * sizeof(*scopeclass));
	}
	scopeclass[nscope] = isclass;
	scopebraces[nscope++] = braces;
	scopelevel = braces;
}

/* leave the bodies of the classes and namespaces closed by the last '}' */
static void
popscopes(void)
{
	while (nscope > 0 && braces < scopebraces[nscope - 1]) {
		--nscope;
	}
	scopelevel = nscope > 0 ? scopebraces[nscope - 1] : 0;
}

#define MY_YY_ALLOCSTEP 1000
static void
my_yymore(void)
{
	static size_t yytext_size = 0;
	
	/* my_yytext is an ever-growing buffer. It will not ever
	 * shrink, nor will it be freed at end of program, for now */
	while (my_yyleng + yyleng + 1 >= yytext_size) {
		my_yytext = myrealloc(my_yytext, yytext_size += MY_YY_ALLOCSTEP);
	}
	
	strncpy (my_yytext + my_yyleng, yytext, yyleng+1);
	my_yyleng += yyleng;
}
