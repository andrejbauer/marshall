(* \section{Main module (module [Main])} *)

module Make =
  functor (D : Dyadic.DYADIC) ->
    struct
      module S = Syntax.Make(D)
      open S
      open Message
      module TC = Typecheck.Make(D)
      module E = Eval.Make(D)
      module ENV = Environment.Make(D)
      module P = Parser.Make(D)
      module L = Lexer.Make(D)

      (* Exception [Fatal_error] is raised when further evaluation is
	impossible. *)
      exception Fatal_error of string

      (* [fatal_error msg] raises exception [Fatal_error msg]. *)
      let fatal_error msg = raise (Fatal_error msg)

      let initial_prec = 32

      (* [exec_cmd (ctx,env) e] executes toplevel command [c] in global
	environment [env] and typing context [ctx]. It prints the result on
	standard output and return the new environment. *)

      let rec exec_cmd ((ctx,env) as ce) = function
	| Expr (e, trace) ->
	    (try
	      let ty = TC.type_of ctx e in
	      let v1, v2 = E.eval trace initial_prec env e in
		print_endline ("- : " ^ string_of_type ty ^ " = " ^ string_of_expr v2) ;
		ce
	    with error -> (Message.report error; ce))
	| Definition (x, e) ->
	    (try
	      let ty = TC.type_of ctx e in
	      let v1, v2 = E.eval false initial_prec env e in
		print_endline
		  (string_of_name x ^ " : " ^ string_of_type ty ^ " = " ^ string_of_expr v2) ;
		((x,ty)::ctx, ENV.extend x v1 env)
	    with error -> (Message.report error; ce))
	| Precision q ->
	    E.target_precision := q ;
	    print_endline ("Target precision set to " ^ D.to_string q) ;
	    ce
	| Hnf e ->
	    let v = E.hnf ~free:true env e in
	      print_endline (string_of_expr v) ;
	      ce      
	| Quit -> raise End_of_file
	| Use fn -> exec_file ce fn
	    
      (* [exec file (ctx,env) fn] executes the contents of file [fn] in
	global context [ctx] and environment [env]. It prints results on
	the standard output and returns the new environment. *)

      and exec_file ce fn =
	let fh = open_in fn in
	let lex = Message.lexer_from_channel fn fh in
	  try
	    let cmds = P.toplevel L.token lex in
	      close_in fh ;
	      exec_cmds ce cmds
	  with
	    | Sys.Break -> Message.runtime_error "Interrupted."
	    | Parsing.Parse_error | Failure("lexing: empty token") ->
		Message.syntax_error lex

      (* [exec_cmds (ctx,env) cmds] executes the list of commands [cmds] in
	context [ctx] and environment [env], and returns the new
	environment. *)

      and exec_cmds ce cmds =
	List.fold_left exec_cmd ce cmds

      (* [shell (ctx,env)] runs the interactive shell in context [ctx] and
	environment [env]. *)

      let shell ce =
	print_string ("Marshall. Press ") ;
	print_string (match Sys.os_type with
			  "Unix" | "Cygwin" -> "Ctrl-D"
			| "Win32" -> "Ctrl-Z"
			| _ -> "EOF") ;
	print_endline " to exit." ;
	print_endline ("\nTop level commands:\n" ^
			" $use \"<filename>\" ... evaluate expressions in file <filename>.\n" ^
			" $trace <expr> ......... trace execution of an expression.\n" ^
			" $precision d .......... set output precision to dyadic constant d.\n" ^
			" $quit ................. exit"
		      ) ;
	print_endline ("\nPress Ctrl-C to interrupt evaluation at any point.") ;
	let global_ctx_env = ref ce in
	  try
	    while true do
	      try
		print_string "Marshall> ";
		let str = read_line () in
		let lex = Message.lexer_from_string str in
		  (* parse a list of commands and print them *)
		let cmds =
		  try
		    P.toplevel L.token lex
		  with
		    | Failure("lexing: empty token")
		    | Parsing.Parse_error -> fatal_error (Message.syntax_error lex)
		in
		let ce = exec_cmds !global_ctx_env cmds in
		  (* set the new global environment *)
		  global_ctx_env := ce
	      with error -> Message.report error
	    done 
	  with
	      End_of_file -> print_endline "\nGood bye."

      (* Main program *)

      let main =
	Sys.catch_break true ;
	let noninteractive = ref false in
	let files = ref [] in
	  Arg.parse
	    [("-n", Arg.Set noninteractive, "do not run interactive shell")]
	    (fun f -> files := f :: !files)
	    "Usage: marshall [-n] [file] ..." ;
	  files := List.rev !files ;
	  let ce =
	    try
	      List.fold_left exec_file ([],[]) !files
	    with error -> (Message.report error; exit 1)
	  in    
	    if not !noninteractive then shell ce
    end;;
