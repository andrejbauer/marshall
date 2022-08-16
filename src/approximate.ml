module Make = functor (D : Dyadic.DYADIC) ->
struct

  module I = Interval.Make(D)
  module Env = Environment.Make(D)
  module S = Syntax.Make(D)

  let error = Message.runtime_error

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


  (* \subsection{Approximants} *)

  (* [lower prec env e] computes the lower approximant of [e] in
     environment [env], computing arithmetical expressions with precision
     [prec]. *)

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
	    let m = S.Dyadic (I.midpoint ~prec 1 s) in
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
	    let m = S.Dyadic (I.midpoint ~prec 1 i) in
	      upper prec (Env.extend x m env) e
	| S.Let (x, e1, e2) ->
	    upper prec (Env.extend x e1 env) e2
	| S.Tuple _ as e -> e
	| S.Proj (e, k) -> proj (approx e) k
	| S.Lambda _ as e -> e
	| S.App (e1, e2) ->
	    let x, e = get_lambda (approx e1) in
	      upper prec (Env.extend x (approx e2) env) e

end;;
