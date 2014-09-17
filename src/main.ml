(** The main program, wrapped as a functor depending on an implementation of dyadics. *)

module Make = functor (D : Dyadic.DYADIC) ->
struct
  module TC = Typecheck.Make(D)
  module E = Eval.Make(D)
  module P = Parser.Make(D)
  module L = Lexer.Make(D)

  let usage = "Usage: marshall [option] ... [file] ..."
  let interactive_shell = ref true
  let prelude = ref true
  let wrapper = ref (Some ["rlwrap"; "ledit"])

let help_text = "Toplevel commands:
#help ;;           print this help
#precision d ;;    set output precision to dyadic constant d
#quit ;;           exit Marshall
#use \"<file>\" ;; evaluate <file>.
#trace <expr> ;;   trace the evaluation of an expression
#hnf <expr> ;;     compute the head-normal form of an expression" ;;

  (** We look for prelude.asd _first_ next to the executable and _then_ in the relevant
      install directory. This makes it easier to experiment with prelude.asd because eff
      will work straight from the build directory. We are probably creating a security hole,
      but we'll deal with that when eff actually gets used by more than a dozen people. *)
  let prelude_file =
    ref (if Sys.file_exists "prelude.asd"
         then Filename.concat (Filename.dirname Sys.argv.(0)) "prelude.asd"
         else Filename.concat Version.marshalldir "prelude.asd")

  (** A list of files to be loaded and run. *)
  let files = ref []

  let add_file interactive filename = (files := (filename, interactive) :: !files)

  (* Command-line options *)
  let options = Arg.align [
    ("--prelude",
     Arg.String (fun str -> prelude_file := str),
     " Specify the prelude.asd file");
    ("--no-prelude",
     Arg.Clear prelude,
     " Do not load pervasives.eff");
    ("--wrapper",
     Arg.String (fun str -> wrapper := Some [str]),
     "<program> Specify a command-line wrapper to be used (such as rlwrap or ledit)");
    ("--no-wrapper",
     Arg.Unit (fun () -> wrapper := None),
     " Do not use a command-line wrapper");
    ("-v",
     Arg.Unit (fun () ->
       print_endline ("Marshall " ^ Version.version ^ "(" ^ Sys.os_type ^ ")") ;
       exit 0),
     " Print version information and exit");
    ("-n",
     Arg.Clear interactive_shell,
     " Do not run the interactive toplevel");
    ("-l",
     Arg.String (fun str -> add_file false str),
     "<file> Load <file> into the initial environment");
  ] ;;

  (* Treat anonymous arguments as files to be run. *)
  let anonymous str =
    add_file true str ;
    interactive_shell := false ;;

  (* Parser wrapper *)
  let parse parser lex =
    try
      parser L.token lex
    with
      | P.Error ->
          Error.syntax ~pos:(L.position_of_lex lex) ""
      | Failure "lexing: empty token" ->
          Error.syntax ~pos:(L.position_of_lex lex) "unrecognised symbol."

  let initial_ctxenv = ([], [])

  (** [exec_cmd interactive (ctx,env) c] executes toplevel command [c] in global
      environment [env] and typing context [ctx]. It prints the result on
      standard output and return the new environment. *)
  let rec exec_cmd interactive (ctx,env) = function
    | E.S.Expr (e, trace) ->
	(try
	   let ty = TC.type_of ctx e in
	   let v1, v2 = E.eval trace env e in
	     print_endline ("- : " ^ E.S.string_of_type ty ^ " = " ^ E.S.string_of_expr v2) ;
	     (ctx, env)
	 with error -> (Message.report error; (ctx, env)))
    | E.S.Definition (x, e) ->
	(try
	   let ty = TC.type_of ctx e in
	   let v1, v2 = E.eval false env e in
	     print_endline
	       (E.S.string_of_name x ^ " : " ^ E.S.string_of_type ty ^ " = " ^ E.S.string_of_expr v2) ;
	     ((x,ty)::ctx, E.Env.extend x v1 env)
	 with error -> (Message.report error; (ctx, env)))
    | E.S.Precision q ->
	E.target_precision := q ;
	print_endline ("Target precision set to " ^ D.to_string q) ;
	(ctx, env)
    | E.S.Hnf e ->
	let v = E.hnf ~free:true env e in
	  print_endline (E.S.string_of_expr v) ;
	  (ctx, env)
    | E.S.Help -> print_endline help_text ; (ctx, env)
    | E.S.Quit -> raise End_of_file
    | E.S.Use fn -> use_file (ctx, env) (fn, interactive)
	
  (** [exec_cmds interactive (ctx,env) cmds] executes the list of commands [cmds] in
      context [ctx] and environment [env], and returns the new
      environment. *)
  and exec_cmds interactive ce cmds =
    List.fold_left (exec_cmd interactive) ce cmds

  and use_file env (filename, interactive) =
    let cmds = L.read_file (parse P.file) filename in
      List.fold_left (exec_cmd interactive) env cmds


  (* Interactive toplevel *)
  let toplevel ctxenv =
    let eof = match Sys.os_type with
      | "Unix" | "Cygwin" -> "Ctrl-D"
      | "Win32" -> "Ctrl-Z"
      | _ -> "EOF"
    in
      print_endline ("Marshall " ^ Version.version);
      print_endline ("[Type " ^ eof ^ " to exit or #help;; for help.]");
      try
        let ctxenv = ref ctxenv in
          while true do
            try
              let cmd = L.read_toplevel (parse P.commandline) () in
                ctxenv := exec_cmd true !ctxenv cmd
            with
              | Error.Error err -> Print.error err
              | Sys.Break -> prerr_endline "Interrupted."
          done
      with End_of_file -> ()

  (** Main program *)
  let main =
    Sys.catch_break true ;
    (* Parse the arguments. *)
    Arg.parse options anonymous usage ;
    (* Attemp to wrap yourself with a line-editing wrapper. *)
    if !interactive_shell then
      begin match !wrapper with
        | None -> ()
        | Some lst ->
            let n = Array.length Sys.argv + 2 in
            let args = Array.make n "" in
              Array.blit Sys.argv 0 args 1 (n - 2) ;
              args.(n - 1) <- "--no-wrapper" ;
              List.iter
                (fun wrapper ->
                   try
                     args.(0) <- wrapper ;
                     Unix.execvp wrapper args
                   with Unix.Unix_error _ -> ())
                lst
      end ;
    (* Files were listed in the wrong order, so we reverse them *)
    files := List.rev !files;
    (* Load the pervasives. *)
    if !prelude then add_file false !prelude_file ;
    try
      (* Run and load all the specified files. *)
      let ctxenv = List.fold_left use_file initial_ctxenv !files in
        if !interactive_shell then toplevel ctxenv
    with
        Error.Error err -> Print.error err; exit 1
end
