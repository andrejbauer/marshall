{
module Lexer =
  functor (D : Dyadic.DYADIC) ->
    struct
      module S = Syntax.Syntax(D)
      module P = Parser.Make(D)
      open P
      open Lexing

      let incr_linenum lexbuf =
	let pos = lexbuf.lex_curr_p in
	  lexbuf.lex_curr_p <-
	    { pos with
		pos_lnum = pos.pos_lnum + 1;
		pos_bol = pos.pos_cnum;
	    }

      let reserved_words = [
	"cut", CUT;
	"exists", EXISTS;
	"exp", EXP;
	"False", FALSE;
	"forall", FORALL;
	"fun", FUN;
	"in", IN;
	"inf", INFINITY;
	"inv", INVERSE;
	"left", LEFT;
	"let", LET;
	"prop", TSIGMA;
	"real", TREAL;
	"right", RIGHT;
	"True", TRUE
      ]
}

let var = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']* '\''*

let mpfr_dec = '-'?
  ((['0' - '9']* '.'? ['0' - '9']+) |
   (['0' - '9']+ '.'? ['0' - '9']*))
  (['e' 'E' '@']? '-'? ['0'-'9']+)?

let mpfr_hex = '-'? ('0'['x' 'X'])
  ((['0' - '9' 'a' - 'f' 'A' - 'F']* '.'? ['0' - '9' 'a' - 'f' 'A' - 'F']+) |
   (['0' - '9' 'a' - 'f' 'A' - 'F']+ '.'? ['0' - '9' 'a' - 'f' 'A' - 'F']*))
  (['e' 'E' 'p' 'P' '@']? '-'? ['0'-'9']+)?

rule token = parse
    [' ' '\t' '\r' '\n'] { token lexbuf }
  | '!' [^'\n']* '\n'    { incr_linenum lexbuf; token lexbuf }
  | '!' [^'\n']* eof     { incr_linenum lexbuf; token lexbuf }
  | ['0'-'9']+           { NATURAL (int_of_string (lexeme lexbuf)) }
  | mpfr_dec             { DYADIC (D.of_string (lexeme lexbuf)) }
  | mpfr_hex             { DYADIC (D.of_string (lexeme lexbuf)) }
  | '#' ['0'-'9']+       { let str = lexeme lexbuf in
			     PROJECT (int_of_string (String.sub str 1 (String.length str - 1)))
			 }
  | '^'                  { POWER }
  | '='                  { EQUAL }
  | '<'                  { LESS }
  | '>'                  { GREATER }
  | "<>"                 { UNEQUAL }
  | '('             	 { LPAREN }
  | ')'             	 { RPAREN }
  | '+'             	 { PLUS }
  | '-'             	 { MINUS }
  | "->"                 { TARROW }
  | "=>"                 { DARROW }
  | '*'             	 { TIMES }
  | '/'             	 { QUOTIENT }
  | '^'                  { POWER }
  | '.'             	 { PERIOD }
  | ':'             	 { COLON }
  | ";;"                 { SEMICOLON2 }
  | ','             	 { COMMA }
  | '{'                  { LBRACE }
  | '}'                  { RBRACE }
  | '['             	 { LBRACK }
  | ']'             	 { RBRACK }
  | "/\\"                { AND }
  | "\\/"                { OR }
  | var             	 { let str = lexeme lexbuf in
			     try List.assoc str reserved_words with Not_found -> VAR (S.Ident str) }
  | "$precision"         { PRECISION }
  | "$use"               { USE }
  | "$trace"             { TRACE }
  | "$quit"              { QUIT }
  | "$hnf"               { HNF }
  | '\"' [^'\"']* '\"'   { let str = lexeme lexbuf in STRING (String.sub str 1 (String.length str - 2)) }
  | eof             	 { EOF }
  | ';'			 { END }

{
    end;;
}
