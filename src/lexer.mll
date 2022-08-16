{
module Make = functor (D : Dyadic.DYADIC) ->
struct
  module S = Syntax.Make(D)
  module P = Parser.Make(D)
  open Lexing
  open P

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

  let position_of_lex lex =
    Common.Position (Lexing.lexeme_start_p lex, Lexing.lexeme_end_p lex)
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
  | [' ' '\t']           { token lexbuf }
  | ['\r' '\n']          { incr_linenum lexbuf; token lexbuf }
  | '!' [^'\n']* '\n'    { incr_linenum lexbuf; token lexbuf }
  | '!' [^'\n']* eof     { incr_linenum lexbuf; token lexbuf }
  | ['0'-'9']+           { NATURAL (int_of_string (lexeme lexbuf)) }
  | mpfr_dec             { DYADIC (D.of_string (lexeme lexbuf)) }
  | mpfr_hex             { DYADIC (D.of_string (lexeme lexbuf)) }
  | "#precision"         { PRECISION } (* Pragmas must come before projection. *)
  | "#use"               { USE }
  | "#trace"             { TRACE }
  | "#quit"              { QUIT }
  | "#hnf"               { HNF }
  | "#help"              { HELP }
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
  | ':'             	 { COLON }
  | ";;"                 { SEMISEMI }
  | ','             	 { COMMA }
  | '{'                  { LBRACE }
  | '}'                  { RBRACE }
  | '['             	 { LBRACK }
  | ']'             	 { RBRACK }
  | "/\\"                { AND }
  | "\\/"                { OR }
  | var             	 { let str = lexeme lexbuf in
			     try List.assoc str reserved_words with Not_found -> VAR (S.Ident str) }
  | '\"' [^'\"']* '\"'   { let str = lexeme lexbuf in STRING (String.sub str 1 (String.length str - 2)) }
  | eof             	 { EOF }

{
  let read_file parser fn =
  try
    let fh = open_in fn in
    let lex = from_channel fh in
    lex.lex_curr_p <- {lex.lex_curr_p with pos_fname = fn};
    try
      let terms = parser lex in
      close_in fh;
      terms
    with
      (* Close the file in case of any parsing errors. *)
      Error.Error err -> close_in fh; raise (Error.Error err)
  with
    (* Any errors when opening or closing a file are fatal. *)
    Sys_error msg -> Error.fatal "%s" msg

  let read_toplevel parser () =
    let has_semisemi str =
      let in_quote = ref false in
      let last_backslash = ref false in
      let last_semi = ref false in
      let semisemi = ref false in
      let i = ref 0 in
      while !i < String.length str && not !semisemi do
        begin
          match str.[!i], !last_backslash, !in_quote, !last_semi with
            | '\\', b, _, _ -> last_backslash := not b; last_semi := false
            | '"', false, b, _ -> in_quote := not b; last_backslash := false; last_semi := false
            | ';', false, false, b -> semisemi := b; last_semi := true
            | _, _, _, _ -> last_backslash := false; last_semi := false
        end ;
        incr i
      done ;
      if !semisemi then
        Some (String.sub str 0 !i)
      else
        None
    in

    let rec read_more prompt acc =
      match has_semisemi acc with
      | Some acc -> acc
      | None ->
          print_string prompt ;
          let str = read_line () in
          read_more "  " (acc ^ "\n" ^ str)
    in

    let str = read_more "# " "" in
    let lex = Lexing.from_string (str ^ "\n") in
    let cmd = parser lex in
      cmd
end
}
