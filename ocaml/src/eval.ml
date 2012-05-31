(* \section{Evaluation (module [Eval])} *)

module Eval =
  functor (D : Dyadic.DYADIC) ->
    struct

      module I = Interval.Interval(D)
      module E = Environment.Environment(D)
      module S = Syntax.Syntax(D)
      open S

      let error = Message.runtime_error

      (* The target precision for top-level evaluation of real
	numbers. Default is 53 bits, like floating-point. *)

      let target_precision = ref (D.make_int ~prec:10 ~round:D.up 1 (-53))

      (* Given precision [prec] and interval [i], compute a precision which
	is better than [prec] and is suitable for working with intervals of
	width [i]. *)

      let make_prec prec i =
	let w = I.width ~prec:2 ~round:D.up i in
	let e1 = D.get_exp w in
	let e2 = max (D.get_exp (I.lower i)) (D.get_exp (I.upper i)) in
	  max 2 (max prec (- 5 * (e1 - e2) / 4))

      (* \subsection{Auxiliary functions} *)

      (* Get the interval approximation of a simple numerical expression. *)

      let get_interval = function
	| Interval i -> i
	| Dyadic q -> I.of_dyadic q
	| Cut (_, i, _, _) -> i
	| e -> error ("Numerical constant expected but got " ^ string_of_expr e)

      (* Get the bound variable and the matrix of an abstraction. *)

      let get_lambda = function
	| Lambda (x, _, e) -> x, e
	| _ -> error "Function expected"

      (* Project from a tuple. *)

      let proj e k =
	match e with
	  | Tuple lst ->
	      (try
		List.nth lst k
	      with Failure _ -> error "Tuple too short")
	  | _ -> error "Tuple expected"

      (* Apply a binary artithmetical operator with precision [prec]. The
	rounding mode, which is [Dyadic.down] or [Dyadic.up] tells whether
	we want a lower or an upper approximant. *)

      let bin_apply ~prec ~round op i1 i2 =
	match op with
	  | Plus -> I.add ~prec ~round i1 i2
	  | Minus -> I.sub ~prec ~round i1 i2
	  | Times -> I.mul ~prec ~round i1 i2
	  | Quotient -> I.div ~prec ~round i1 i2

      (* Apply a unary operator, see [bin_apply] for explanation of [prec]
	and [round]. *)

      let unary_apply ~prec ~round op i =
	match op with
	  | Opposite -> I.neg ~prec ~round i
	  | Inverse -> I.inv ~prec ~round i
	  (*| Exp -> I.exp ~prec ~round i*)

      (* [Break] is used to shortcircuit evaluation of conjunctions and
	disjunctions. *)

      exception Break

      (* [fold_and f [x1,...,xn]] constructs the conjunction [And [f x1;
	..., f xn]]. It throws out [True]'s and shortcircuits on
	[False]. *)

      let fold_and f lst =
	let rec fold acc = function
	  | [] -> acc
	  | p::ps ->
	      (match f p with
		| True -> fold acc ps
		| False -> raise Break
		| q -> fold (q::acc) ps)
	in
	  try
	    match fold [] lst with
	      | [] -> True
	      | lst -> And (List.rev lst)
	  with Break -> False

      (* [fold_or f [x1,...,xn]] constructs the disjunction [Or [f x1;
	..., f xn]]. It throws out [False]'s and shortcircuits on
	[True]. *)

      let fold_or f lst =
	let rec fold acc = function
	  | [] -> acc
	  | p::ps ->
	      (match f p with
		| True -> raise Break
		| False -> fold acc ps
		| q -> fold (q::acc) ps)
	in
	  try
	    match fold [] lst with
	      | [] -> False
	      | lst -> Or (List.rev lst)
	  with Break -> True

      (* [make_exists x i p] constructs the existential quantifier [Exists (x,i,p)]
	over an inhabited interval [i]. If [p] is [True] or [False] it shortcircuits
	the quantifier. *)

      let make_exists x i p =
	assert (I.forward i) ;
	if p = True then
	  True
	else if p = False then
	  False
	else
	  Exists (x, i, p)

      (* [make_forall x i p] constructs the universal quantifier [Forall (x,i,p)]
	over an inhabited interval [i]. If [p] is [True] or [False] it shortcircuits
	the quantifier. *)

      let make_forall x i p =
	assert (I.forward i) ;
	if p = True then
	  True
	else if p = False then
	  False
	else
	  Forall (x, i, p)

      (* \subsection{Approximants} *)

      (* [lower prec env e] computes the lower approximant of [e] in
	environment [env], computing arithmetical expressions with precision
	[prec]. *)

      let string_of_env env =
	String.concat "\n" (List.map (fun (x,v) -> string_of_name x ^ "=" ^ string_of_expr v) env)

      let rec lower prec env e =
	let approx = lower prec env in
	  match e with
	    | Var x -> approx (E.get x env)
	    | RealVar (_, i) -> Interval i
	    | Dyadic q -> Interval (I.of_dyadic q)
	    | Interval _ as e -> e
	    | Cut (_, i, _, _) -> Interval i
	    | Binary (op, e1, e2) ->
		let i1 = get_interval (approx e1) in
		let i2 = get_interval (approx e2) in
		  Interval (bin_apply ~prec ~round:D.down op i1 i2)
	    | Unary (op, e) ->
		let i = get_interval (approx e) in
		  Interval (unary_apply ~prec ~round:D.down op i)
	    | Power (e, k) ->
		let i = get_interval (approx e) in
		  Interval (I.pow ~prec ~round:D.down i k)
	    | True -> True
	    | False -> False
	    | Less (e1, e2) ->
		let i1 = get_interval (approx e1) in
		let i2 = get_interval (approx e2) in
		  if D.lt (I.upper i1) (I.lower i2) then
		    True
		  else
		    False
	    | And lst -> fold_and approx lst
	    | Or lst -> fold_or approx lst
	    | Exists (x, s, e) ->
		let m = Dyadic (I.midpoint prec 1 s) in
		  lower prec (E.extend x m env) e
	    | Forall (x, i, e) ->
		lower prec (E.extend x (Interval i) env) e
	    | Let (x, e1, e2) ->
		lower prec (E.extend x (approx e1) env) e2
	    | Tuple _ as e -> e
	    | Proj (e, k) -> proj (approx e) k
	    | Lambda _ as e -> e
	    | App (e1, e2) ->
		let x, e = get_lambda (approx e1) in
		  lower prec (E.extend x (approx e2) env) e


      (* Function [upper prec env e] computes the upper approximant of [e]
	in environment [env], computing arithmetical expressions with
	precision [prec]. *)

      let rec upper prec env e =
	let approx = upper prec env in
	  match e with
	    | Var x -> approx (E.get x env)
	    | RealVar (_, i) -> Interval (I.flip i)
	    | Dyadic q -> Interval (I.of_dyadic q)
	    | Interval _ as e -> e
	    | Cut (_, i, _, _) -> Interval (I.flip i)
	    | Binary (op, e1, e2) ->
		let i1 = get_interval (approx e1) in
		let i2 = get_interval (approx e2) in
		  Interval (bin_apply ~prec ~round:D.up op i1 i2)
	    | Unary (op, e) ->
		let i = get_interval (approx e) in
		  Interval (unary_apply ~prec ~round:D.up op i)
	    | Power (e, k) ->
		let i = get_interval (approx e) in
		  Interval (I.pow ~prec ~round:D.up i k)
	    | True -> True
	    | False -> False
	    | Less (e1, e2) ->
		let i1 = get_interval (approx e1) in
		let i2 = get_interval (approx e2) in
		  if D.lt (I.upper i1) (I.lower i2) then
		    True
		  else
		    False
	    | And lst -> fold_and approx lst
	    | Or lst -> fold_or approx lst
	    | Exists (x, i, e) ->
		let j = I.flip i in
		  upper prec (E.extend x (Interval j) env) e
	    | Forall (x, i, e) ->
		let m = Dyadic (I.midpoint prec 1 i) in
		  upper prec (E.extend x m env) e
	    | Let (x, e1, e2) ->
		upper prec (E.extend x e1 env) e2
	    | Tuple _ as e -> e
	    | Proj (e, k) -> proj (approx e) k
	    | Lambda _ as e -> e
	    | App (e1, e2) ->
		let x, e = get_lambda (approx e1) in
		  upper prec (E.extend x (approx e2) env) e

      (* \subsection{Evaluation} *)

      (* The general strategy for evaluation is to successively
	\emph{refine} a closed expressoin until it reaches a satisfactory
	form. An expression of type [Ty_Real] is `satisfactory' if its
	lower approximant is narrow enough (see the [\$precision]
	toplevel command). An proposition is satisfactory if it is [True]
	or [False]. Tuples are satisfactory, i.e., they are evaluated
	lazily (but the top-level [eval] evaluates top-level tuples to make
	the user happy). A $\lambda$-abstraction is not evaluated.
      *)

      (* The first step of evaluation is to evaluate to head-normal form
	because we want to get rid of local definitions and redexes. This
	causes a huge inefficiency because it may unnecessarily multiply
	repeat subexpressions, but computation of derivatives cannot handle
	general applications and local definitions. *)

      let rec hnf ?(free=false) env e =
	let hnf = hnf ~free in
	  match e with
	    | Var x ->
		(try
		  List.assoc x env
		with Not_found ->
		  if free then Var x else error ("Unknown variable " ^ string_of_name x))
	    | (RealVar _ | Dyadic _ | Interval _ | True | False) as e -> e
	    | Cut (x, i, p1, p2) -> 
		let env' = E.extend x (Var x) env in
		  Cut (x, i, hnf env' p1, hnf env' p2)
	    | Binary (op, e1, e2) -> Binary (op, hnf env e1, hnf env e2)
	    | Unary (op, e) -> Unary (op, hnf env e)
	    | Power (e, k) -> Power (hnf env e, k)
	    | Proj (e, k) -> 
		(match hnf env e with
		  | Tuple _ as e' -> proj e' k
		  | e' -> Proj (e', k))
	    | Less (e1, e2) -> Less (hnf env e1, hnf env e2)
	    | And lst -> And (List.map (hnf env) lst)
	    | Or lst -> Or (List.map (hnf env) lst)
	    | Tuple lst -> Tuple (List.map (hnf env) lst)
	    | Lambda (x, ty, e) -> Lambda (x, ty, hnf (E.extend x (Var x) env) e)
	    | Exists (x, i, e) -> Exists (x, i, hnf (E.extend x (Var x) env) e)
	    | Forall (x, i, e) -> Forall (x, i, hnf (E.extend x (Var x) env) e)
	    | App (e1, e2)  ->
		let e2' = hnf env e2 in
		  (match hnf env e1 with
		    | Lambda (x, ty, e) -> hnf (E.extend x e2' env) e
		    | e1' -> App (e1', e2'))
	    | Let (x, e1, e2) -> 
		let e1' = hnf env e1 in
		  hnf (E.extend x e1' env) e2

      (* The function [refine k prec env e] performs one step of evaluation
	of expression [e] in environment [env], using precision [prec] to
	compute arithmetical expressions. This is used by [eval] below to
	make progress.  The counter [k] tells which successive refinement
	this is.

	We need to be able to refine expressions which contain free
	variables (in order to refine cuts and quantifiers). For this
	purpose we have a special expression [RealVar (x,i)] which denotes
	free variable [x] ranging over interval [i].
      *)

      let rec refine k prec env e =
	let refn = refine k prec env in
	  if lower prec env e = True then True
	  else if upper prec env e = False then False
	  else
	    match e with
	      | Var x -> refine k prec env (E.get x env)
	      | RealVar (x, _) -> Var x
	      | Dyadic _ -> e
	      | Interval _ -> e
	      | Cut (x, i, p1, p2) -> begin
		  let prec = make_prec prec i in
		    (* To refine a cut [Cut(x,i,p1,p2)] we try to make the
		      interval [i] smaller and refine [p1] and [p2]. *)
		  let a = I.lower i in
		  let b = I.upper i in
		    (* Bisection *)
		  let m1, m2 = I.thirds prec k i in
		  let a' = (if lower prec (E.extend x (Dyadic m1) env) p1 = True then m1 else a) in
		  let b' = (if lower prec (E.extend x (Dyadic m2) env) p2 = True then m2 else b) in
		    (* Newton's method would come. See revision 259 (for a faulty version). *)
		    match D.cmp a' b' with
		      | `less ->
			  (* The new interval *)
			  let j = I.make a' b' in
			  let env' = E.extend x (RealVar (x, j)) env in
			  let q1 = refine k prec env' p1 in
			  let q2 = refine k prec env' p2 in
			    Cut (x, j, q1, q2)
		      | `equal ->
			  (* We found an exact value *)
			  Dyadic a'
		      | `greater ->
			  (* We have a backwards cut. Do nothing. Someone should think
			    whether this is ok. It would be nice if cuts could be
			    overlapping, but I have not thought whether this would break
			    anything else.
			  *)
			  e
		end
	      | Binary (op, e1, e2) -> Binary (op, refn e1, refn e2)
	      | Unary (op, e) -> Unary (op, refn e)
	      | Power (e, k) -> Power (refn e, k)
	      | True -> True
	      | False -> False
	      | Less (e1, e2) -> Less (refn e1, refn e2)
	      | And lst -> fold_and refn lst
	      | Or lst -> fold_or refn lst
	      | Exists (x, i, p) ->
		  let prec = make_prec prec i in
		  let q = refine k prec (E.extend x (RealVar (x, i)) env) p in
		  let i1, i2 = I.split prec 1 i in
		    (* We could use Newton's method here. See revision 259. *)
		    fold_or (fun i -> make_exists x i q) [i1; i2]

	      | Forall (x, i, p) ->
		  let prec = make_prec prec i in
		  let q = refine k prec (E.extend x (RealVar (x, i)) env) p in
		  let i1, i2 = I.split prec 1 i in
		    (* We could use Newton's method here. See revision 259. *)
		    fold_and (fun i -> make_forall x i q) [i1; i2]
	      | Let (x, e1, e2) ->
		  refine k prec (E.extend x (refn e1) env) e2
	      | Tuple _ -> e
	      | Proj (e, k) ->
		  (match refn e with
		    | Tuple lst ->
			(try
			    refn (List.nth lst k)
			  with Failure _ -> error "Tuple too short")
		    | e -> Proj (e, k))
	      | Lambda _ -> e
	      | App (e1, e2) ->
		  (match refn e1 with
		    | Lambda (x, _, e) -> refine k prec (E.extend x (refn e2) env) e
		    | e -> App (e, e2))

      (* [eval prec env e] evaluates expression [e] in environment [env] by
	repeatedly calling [refine]. It increases precision at each step,
	although we should do something more intelligent about that (not
	all subexpressions of [e] need the same precision). The argument
	[trace] determines whether debugging information should be printed
	out. *)

      let eval trace prec env e =
	let rec loop k p e =
	  if trace then
	    begin
	      print_endline ("--------------------------------------------------\n" ^
			      "Iteration: " ^ string_of_int k ^ "\n" ^
			      string_of_expr e ^ "\n" ^
			      "Press Enter to continue " 
			    ) ;
	      ignore (read_line ())	  
	    end ;
	  match e with
	    | Var _ | RealVar _
	    | Less _ | And _ | Or _ | Exists _ | Forall _
	    | Let _ | Proj _ | App _ ->
		loop (k+1) (p+1) (refine k p env e)
	    | Binary _ | Unary _ | Power _ | Cut _ ->
		(match lower p env e with
		  | Interval i ->
		      let w = (I.width 10 D.up i) in
			if D.lt w !target_precision then
			  (e, Interval i)
			else
			  loop (k+1) (make_prec (p+3) (I.make D.zero !target_precision)) (refine k p env e)
		  | _ -> assert false)
	    | Dyadic _ | Interval _ | True | False | Lambda _ -> (e, e)
	    | Tuple lst -> 
		let lst1, lst2 =
		  List.fold_left
		    (fun (lst1, lst2) e ->
		      let v1, v2 = loop k p e in
			v1::lst1, v2::lst2)
		    ([], [])
		    lst
		in
		  (Tuple lst1, Tuple lst2)
	in
	  loop 1 prec (hnf env e)
    end;;

