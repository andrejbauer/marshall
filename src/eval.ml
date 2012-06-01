(* \section{Evaluation (module [Eval])} *)

module Make = functor (D : Dyadic.DYADIC) ->
struct

  module I = Interval.Make(D)
  module Env = Environment.Make(D)
  module S = Syntax.Make(D)

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
    | S.Interval i -> i
    | S.Dyadic q -> I.of_dyadic q
    | S.Cut (_, i, _, _) -> i
    | e -> error ("Numerical constant expected but got " ^ S.string_of_expr e)

  (* Get the bound variable and the matrix of an abstraction. *)

  let get_lambda = function
    | S.Lambda (x, _, e) -> x, e
    | _ -> error "Function expected"

  (* Project from a tuple. *)

  let proj e k =
    match e with
      | S.Tuple lst ->
	  (try
	     List.nth lst k
	   with Failure _ -> error "Tuple too short")
      | _ -> error "Tuple expected"

  (* Apply a binary artithmetical operator with precision [prec]. The
     rounding mode, which is [Dyadic.down] or [Dyadic.up] tells whether
     we want a lower or an upper approximant. *)

  let bin_apply ~prec ~round op i1 i2 =
    match op with
      | S.Plus -> I.add ~prec ~round i1 i2
      | S.Minus -> I.sub ~prec ~round i1 i2
      | S.Times -> I.mul ~prec ~round i1 i2
      | S.Quotient -> I.div ~prec ~round i1 i2

  (* Apply a unary operator, see [bin_apply] for explanation of [prec]
     and [round]. *)

  let unary_apply ~prec ~round op i =
    match op with
      | S.Opposite -> I.neg ~prec ~round i
      | S.Inverse -> I.inv ~prec ~round i
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
	     | S.True -> fold acc ps
	     | S.False -> raise Break
	     | q -> fold (q::acc) ps)
    in
      try
	match fold [] lst with
	  | [] -> S.True
	  | lst -> S.And (List.rev lst)
      with Break -> S.False

  (* [fold_or f [x1,...,xn]] constructs the disjunction [Or [f x1;
     ..., f xn]]. It throws out [False]'s and shortcircuits on
     [True]. *)

  let fold_or f lst =
    let rec fold acc = function
      | [] -> acc
      | p::ps ->
	  (match f p with
	     | S.True -> raise Break
	     | S.False -> fold acc ps
	     | q -> fold (q::acc) ps)
    in
      try
	match fold [] lst with
	  | [] -> S.False
	  | lst -> S.Or (List.rev lst)
      with Break -> S.True

  (* [make_exists x i p] constructs the existential quantifier [Exists (x,i,p)]
     over an inhabited interval [i]. If [p] is [True] or [False] it shortcircuits
     the quantifier. *)

  let make_exists x i p =
    assert (I.forward i) ;
    if p = S.True then
      S.True
    else if p = S.False then
      S.False
    else
      S.Exists (x, i, p)

  (* [make_forall x i p] constructs the universal quantifier [Forall (x,i,p)]
     over an inhabited interval [i]. If [p] is [True] or [False] it shortcircuits
     the quantifier. *)

  let make_forall x i p =
    assert (I.forward i) ;
    if p = S.True then
      S.True
    else if p = S.False then
      S.False
    else
      S.Forall (x, i, p)

  (* \subsection{Approximants} *)

  (* [lower prec env e] computes the lower approximant of [e] in
     environment [env], computing arithmetical expressions with precision
     [prec]. *)

  let string_of_env env =
    String.concat "\n" (List.map (fun (x,v) -> S.string_of_name x ^ "=" ^ S.string_of_expr v) env)

  let rec lower prec env e =
    let approx = lower prec env in
      match e with
	| S.Var x -> approx (Env.get x env)
	| S.RealVar (_, i) -> S.Interval i
	| S.Dyadic q -> S.Interval (I.of_dyadic q)
	| S.Interval _ as e -> e
	| S.Cut (_, i, _, _) -> S.Interval i
	| S.Binary (op, e1, e2) ->
	    let i1 = get_interval (approx e1) in
	    let i2 = get_interval (approx e2) in
	      S.Interval (bin_apply ~prec ~round:D.down op i1 i2)
	| S.Unary (op, e) ->
	    let i = get_interval (approx e) in
	      S.Interval (unary_apply ~prec ~round:D.down op i)
	| S.Power (e, k) ->
	    let i = get_interval (approx e) in
	      S.Interval (I.pow ~prec ~round:D.down i k)
	| S.True -> S.True
	| S.False -> S.False
	| S.Less (e1, e2) ->
	    let i1 = get_interval (approx e1) in
	    let i2 = get_interval (approx e2) in
	      if D.lt (I.upper i1) (I.lower i2) then
		S.True
	      else
		S.False
	| S.And lst -> fold_and approx lst
	| S.Or lst -> fold_or approx lst
	| S.Exists (x, s, e) ->
	    let m = S.Dyadic (I.midpoint prec 1 s) in
	      lower prec (Env.extend x m env) e
	| S.Forall (x, i, e) ->
	    lower prec (Env.extend x (S.Interval i) env) e
	| S.Let (x, e1, e2) ->
	    lower prec (Env.extend x (approx e1) env) e2
	| S.Tuple _ as e -> e
	| S.Proj (e, k) -> proj (approx e) k
	| S.Lambda _ as e -> e
	| S.App (e1, e2) ->
	    let x, e = get_lambda (approx e1) in
	      lower prec (Env.extend x (approx e2) env) e


  (* Function [upper prec env e] computes the upper approximant of [e]
     in environment [env], computing arithmetical expressions with
     precision [prec]. *)

  let rec upper prec env e =
    let approx = upper prec env in
      match e with
	| S.Var x -> approx (Env.get x env)
	| S.RealVar (_, i) -> S.Interval (I.flip i)
	| S.Dyadic q -> S.Interval (I.of_dyadic q)
	| S.Interval _ as e -> e
	| S.Cut (_, i, _, _) -> S.Interval (I.flip i)
	| S.Binary (op, e1, e2) ->
	    let i1 = get_interval (approx e1) in
	    let i2 = get_interval (approx e2) in
	      S.Interval (bin_apply ~prec ~round:D.up op i1 i2)
	| S.Unary (op, e) ->
	    let i = get_interval (approx e) in
	      S.Interval (unary_apply ~prec ~round:D.up op i)
	| S.Power (e, k) ->
	    let i = get_interval (approx e) in
	      S.Interval (I.pow ~prec ~round:D.up i k)
	| S.True -> S.True
	| S.False -> S.False
	| S.Less (e1, e2) ->
	    let i1 = get_interval (approx e1) in
	    let i2 = get_interval (approx e2) in
	      if D.lt (I.upper i1) (I.lower i2) then
		S.True
	      else
		S.False
	| S.And lst -> fold_and approx lst
	| S.Or lst -> fold_or approx lst
	| S.Exists (x, i, e) ->
	    let j = I.flip i in
	      upper prec (Env.extend x (S.Interval j) env) e
	| S.Forall (x, i, e) ->
	    let m = S.Dyadic (I.midpoint prec 1 i) in
	      upper prec (Env.extend x m env) e
	| S.Let (x, e1, e2) ->
	    upper prec (Env.extend x e1 env) e2
	| S.Tuple _ as e -> e
	| S.Proj (e, k) -> proj (approx e) k
	| S.Lambda _ as e -> e
	| S.App (e1, e2) ->
	    let x, e = get_lambda (approx e1) in
	      upper prec (Env.extend x (approx e2) env) e

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
	| S.Var x ->
	    (try
	       List.assoc x env
	     with Not_found ->
	       if free then S.Var x else error ("Unknown variable " ^ S.string_of_name x))
	| (S.RealVar _ | S.Dyadic _ | S.Interval _ | S.True | S.False) as e -> e
	| S.Cut (x, i, p1, p2) -> 
	    let env' = Env.extend x (S.Var x) env in
	      S.Cut (x, i, hnf env' p1, hnf env' p2)
	| S.Binary (op, e1, e2) -> S.Binary (op, hnf env e1, hnf env e2)
	| S.Unary (op, e) -> S.Unary (op, hnf env e)
	| S.Power (e, k) -> S.Power (hnf env e, k)
	| S.Proj (e, k) -> 
	    (match hnf env e with
	       | S.Tuple _ as e' -> proj e' k
	       | e' -> S.Proj (e', k))
	| S.Less (e1, e2) -> S.Less (hnf env e1, hnf env e2)
	| S.And lst -> S.And (List.map (hnf env) lst)
	| S.Or lst -> S.Or (List.map (hnf env) lst)
	| S.Tuple lst -> S.Tuple (List.map (hnf env) lst)
	| S.Lambda (x, ty, e) -> S.Lambda (x, ty, hnf (Env.extend x (S.Var x) env) e)
	| S.Exists (x, i, e) -> S.Exists (x, i, hnf (Env.extend x (S.Var x) env) e)
	| S.Forall (x, i, e) -> S.Forall (x, i, hnf (Env.extend x (S.Var x) env) e)
	| S.App (e1, e2)  ->
	    let e2' = hnf env e2 in
	      (match hnf env e1 with
		 | S.Lambda (x, ty, e) -> hnf (Env.extend x e2' env) e
		 | e1' -> S.App (e1', e2'))
	| S.Let (x, e1, e2) -> 
	    let e1' = hnf env e1 in
	      hnf (Env.extend x e1' env) e2

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
      if lower prec env e = S.True then S.True
      else if upper prec env e = S.False then S.False
      else
	match e with
	  | S.Var x -> refine k prec env (Env.get x env)
	  | S.RealVar (x, _) -> S.Var x
	  | S.Dyadic _ -> e
	  | S.Interval _ -> e
	  | S.Cut (x, i, p1, p2) -> begin
	      let prec = make_prec prec i in
		(* To refine a cut [Cut(x,i,p1,p2)] we try to make the
		   interval [i] smaller and refine [p1] and [p2]. *)
	      let a = I.lower i in
	      let b = I.upper i in
		(* Bisection *)
	      let m1, m2 = I.thirds prec k i in
	      let a' = (if lower prec (Env.extend x (S.Dyadic m1) env) p1 = S.True then m1 else a) in
	      let b' = (if lower prec (Env.extend x (S.Dyadic m2) env) p2 = S.True then m2 else b) in
		(* Newton's method would come. See revision 259 (for a faulty version). *)
		match D.cmp a' b' with
		  | `less ->
		      (* The new interval *)
		      let j = I.make a' b' in
		      let env' = Env.extend x (S.RealVar (x, j)) env in
		      let q1 = refine k prec env' p1 in
		      let q2 = refine k prec env' p2 in
			S.Cut (x, j, q1, q2)
		  | `equal ->
		      (* We found an exact value *)
		      S.Dyadic a'
		  | `greater ->
		      (* We have a backwards cut. Do nothing. Someone should think
			 whether this is ok. It would be nice if cuts could be
			 overlapping, but I have not thought whether this would break
			 anything else.
		      *)
		      e
	    end
	  | S.Binary (op, e1, e2) -> S.Binary (op, refn e1, refn e2)
	  | S.Unary (op, e) -> S.Unary (op, refn e)
	  | S.Power (e, k) -> S.Power (refn e, k)
	  | S.True -> S.True
	  | S.False -> S.False
	  | S.Less (e1, e2) -> S.Less (refn e1, refn e2)
	  | S.And lst -> fold_and refn lst
	  | S.Or lst -> fold_or refn lst
	  | S.Exists (x, i, p) ->
	      let prec = make_prec prec i in
	      let q = refine k prec (Env.extend x (S.RealVar (x, i)) env) p in
	      let i1, i2 = I.split prec 1 i in
		(* We could use Newton's method here. See revision 259. *)
		fold_or (fun i -> make_exists x i q) [i1; i2]

	  | S.Forall (x, i, p) ->
	      let prec = make_prec prec i in
	      let q = refine k prec (Env.extend x (S.RealVar (x, i)) env) p in
	      let i1, i2 = I.split prec 1 i in
		(* We could use Newton's method here. See revision 259. *)
		fold_and (fun i -> make_forall x i q) [i1; i2]
	  | S.Let (x, e1, e2) ->
	      refine k prec (Env.extend x (refn e1) env) e2
	  | S.Tuple _ -> e
	  | S.Proj (e, k) ->
	      (match refn e with
		 | S.Tuple lst ->
		     (try
			refn (List.nth lst k)
		      with Failure _ -> error "Tuple too short")
		 | e -> S.Proj (e, k))
	  | S.Lambda _ -> e
	  | S.App (e1, e2) ->
	      (match refn e1 with
		 | S.Lambda (x, _, e) -> refine k prec (Env.extend x (refn e2) env) e
		 | e -> S.App (e, e2))

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
			   S.string_of_expr e ^ "\n" ^
			   "Press Enter to continue " 
			) ;
	  ignore (read_line ())	  
	end ;
      match e with
	| S.Var _ | S.RealVar _
	| S.Less _ | S.And _ | S.Or _ | S.Exists _ | S.Forall _
	| S.Let _ | S.Proj _ | S.App _ ->
	    loop (k+1) (p+1) (refine k p env e)
	| S.Binary _ | S.Unary _ | S.Power _ | S.Cut _ ->
	    (match lower p env e with
	       | S.Interval i ->
		   let w = (I.width 10 D.up i) in
		     if D.lt w !target_precision then
		       (e, S.Interval i)
		     else
		       loop (k+1) (make_prec (p+3) (I.make D.zero !target_precision)) (refine k p env e)
	       | _ -> assert false)
	| S.Dyadic _ | S.Interval _ | S.True | S.False | S.Lambda _ -> (e, e)
	| S.Tuple lst -> 
	    let lst1, lst2 =
	      List.fold_left
		(fun (lst1, lst2) e ->
		   let v1, v2 = loop k p e in
		     v1::lst1, v2::lst2)
		([], [])
		lst
	    in
	      (S.Tuple lst1, S.Tuple lst2)
    in
      loop 1 prec (hnf env e)
end;;

