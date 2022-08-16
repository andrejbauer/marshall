(** Error messages *)

(* \subsection{Parsing errors} *)

open Lexing

(* [lexer_from_channel fn ch] returns a lexer stream which takes
   input from channel [ch]. The filename (for reporting errors) is
   set to [fn].
*)
let lexer_from_channel fn ch =
  let lex = Lexing.from_channel ch in
  let pos = lex.lex_curr_p in
    lex.lex_curr_p <- { pos with pos_fname = fn; pos_lnum = 1; } ;
    lex

(* [lexer_from_string str] returns a lexer stream which takes input
   from a string [str]. The filename (for reporting errors) is set to
   [""]. *)
let lexer_from_string str =
  let lex = Lexing.from_string str in
  let pos = lex.lex_curr_p in
    lex.lex_curr_p <- { pos with pos_fname = ""; pos_lnum = 1; } ;
    lex

let string_of_position {pos_fname=fn; pos_lnum=ln; pos_bol=bol; pos_cnum=cn} =
  let c = cn - bol in
    if fn = "" then
      "Character " ^ string_of_int c
    else
      "File \"" ^ fn ^ "\", line " ^ string_of_int ln ^ ", character " ^ string_of_int c

exception SyntaxError of string

let syntax_error {lex_curr_p=pos; _} = raise (SyntaxError (string_of_position pos))

(* \subsection{Type checking errors} *)

exception TypecheckError of string

let typecheck_error msg = raise (TypecheckError msg)

(* \subsection{Runtime errors} *)

exception RuntimeError of string

let runtime_error msg = raise (RuntimeError msg)

(* \subsection{Error reporting} *)

let report err =
  print_endline
    (match err with
       | SyntaxError msg -> "Syntax error: " ^ msg
       | TypecheckError msg -> "Type checking failed: " ^ msg
       | RuntimeError msg -> "Runtime error: " ^ msg
       | End_of_file -> raise End_of_file (* end of file must propagate *)
       | Sys.Break -> "Interrupted by user."
       | exc -> "Unknown error: " ^ (Printexc.to_string exc))
