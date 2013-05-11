module Make = functor (D : Dyadic.DYADIC) ->
struct

  module I = Interval.Make(D)
  module S = Syntax.Make(D)
  module R = Region.Make(D)
  module A = Approximate.Make(D)
  module Env = Environment.Make(D)

  (* \subsection{Newton's method} *)
 
  (* This section is not finished because we have to sort out problems which
     are caused by appearance of back-to-front intervals. *)
  
  (* Does [x] occur freely in [e]? *)
  let rec free x = function
    | S.Var y -> x <> y
    | S.RealVar (y, _) -> x <> y
    | S.Dyadic _
    | S.Interval _
    | S.True
    | S.False -> true
    | S.Cut (y, _, p1, p2) -> x = y || (free x p1 && free x p2)
    | S.Binary (_, e1, e2)
    | S.Less (e1, e2)
    | S.App (e1, e2)  -> free x e1 && free x e2
    | S.Unary (_, e)
    | S.Power (e, _)
    | S.Proj (e, _) -> free x e
    | S.And lst
    | S.Or lst
    | S.Tuple lst -> List.for_all (free x) lst
    | S.Lambda (y, _, e)
    | S.Exists (y, _, e)
    | S.Forall (y, _, e) -> x = y || free x e
    | S.Let (y, e1, e2) -> free x e1 && (x = y || free x e2)
  
  (* Suppose [e] is an expression in environment [env] with a free
     variable [x]. Then [e] as a function of [x] maps a real [x] to an
     interval $[e_1(x), e_2(x)]$.
  
     For estimation of inequalities we need to compute upper and lower
     Lipschitz constants for $e_1(x)$ when $x$ ranges over a given
     interval. This we do by symbolic differentiation.
  
     We assume that the expressions are in head
     normal form and of type real. In particular, this means we are
     never going to see a lambda abstraction, a tuple, a projection, or
     a local definition.
  *)
  
  let zero = S.Dyadic D.zero
  let one = S.Dyadic D.one
  
  let rec diff x = function
    | S.Var y -> if x = y then one else zero
    | S.RealVar (y, _) -> if x = y then one else zero
    | S.Dyadic _ -> zero
    | S.Interval _ -> zero
    | S.Cut (y, i, p1, p2) -> 
        if x = y || S.(free x p1 && free x p2) then
  	zero
        else
  	S.Interval I.bottom
    | S.Binary (S.Plus, e1, e2) -> S.Binary (S.Plus, diff x e1, diff x e2)
    | S.Binary (S.Minus, e1, e2) -> S.Binary (S.Minus, diff x e1, diff x e2)
    | S.Binary (S.Times, e1, e2) -> 
        S.Binary (S.Plus,
  	      S.Binary (S.Times, diff x e1, e2),
  	      S.Binary (S.Times, e1, diff x e2))
    | S.Binary (S.Quotient, e1, e2) ->
        S.Binary (S.Quotient,
  	      S.Binary (S.Minus,
  		      S.Binary (S.Times, diff x e1, e2),
  		      S.Binary (S.Times, e1, diff x e2)),
  	      S.Power (e2, 2))
    | S.Unary (S.Opposite, e) -> S.Unary (S.Opposite, diff x e)
    | S.Unary (S.Inverse, e) -> S.Binary (S.Quotient, diff x e, S.Power (e, 2))
    (*| S.Unary (S.Exp, e) -> S.Binary (S.Times, S.Unary (S.Exp, e), diff x e)*)
    | S.Power (e, 0) -> zero
    | S.Power (e, 1) -> diff x e
    | S.Power (e, k) ->
        S.Binary (S.Times,
  	      S.Dyadic (D.of_int ~round:D.down k),
  	      S.Binary (S.Times,
  		      S.Power (e, k-1),
  		      diff x e))
    | S.True
    | S.False
    | S.Less _
    | S.And _
    | S.Or _
    | S.Exists _
    | S.Forall _ -> Error.runtime "Cannot differentiate a proposition"
    | S.Let (y, e1, e2) -> Error.runtime "Cannot differentiate a local definition"
    | S.Tuple _ -> failwith "Cannot differentiate a tuple"
    | S.Proj (_, _) -> failwith "Cannot differentiate a projection"
    | S.Lambda (x, ty, e) -> failwith "Cannot differentiate an abstraction"
    | S.App (e1, e2) -> failwith "Cannot differentiate a redex"
  
  (* The function [estimate_positive env i x e] returns a set such that
     in environment [env] the expression [e] with free variable [x]
     ranging over interval [i] we have [0 < e] everywhere on the set. It
     uses interval Newton's method.
  *)
  
  let estimate_positive prec env x i e =
    (* For infinite intervals we give up. We could try to do something
       more intelligent, such as computing the derivative at infinity
       (using a suitable transformation which moves infinity to a finite
       point). *)
    if not (I.proper i) then
      R.empty
    else
      let a = I.lower i in
      let y = A.get_interval (A.lower prec (Env.extend x (S.Dyadic a) env) e) in
      let d = A.get_interval (A.lower prec (Env.extend x (S.Interval i) env) (diff x e)) in
      let yl = I.lower y in
      let dl = I.lower d in
        match D.sgn dl with
  	| `negative ->
  	    let b' = D.sub ~prec ~round:D.down a (D.div ~prec ~round:D.up yl dl) in
  	      R.intersection
  		(R.of_interval i)
  		(R.open_left_ray b')
  	| `zero ->
  	    (match D.sgn yl with
  	       | `negative | `zero -> R.empty
  	       | `positive -> R.of_interval i)
  	| `positive ->
  	    let a' = D.sub ~prec ~round:D.up a (D.div ~prec ~round:D.down yl dl) in
  	      R.intersection
  		(R.of_interval i)
  		(R.open_right_ray a')
  
  (* The function [estimate_non_positive env i x e] returns a
     set such that in environment [env] the expression [e] with
     free variable [x] ranging over interval [i] is guaranteed to be
     non-positive everywhere on the set.
  *)
  
  let estimate_non_positive k prec env x i e =
    (* For infinite intervals we give up. We could try to do something
       more intelligent, such as computing the derivative at infinity
       (using a suitable transformation which moves infinity to a finite
       point). *)
    if not (I.proper i) then
      R.empty
    else
      let a = I.lower i in
      let y = A.get_interval (A.upper prec (Env.extend x (S.Dyadic a) env) e) in
      let d = A.get_interval (A.upper prec (Env.extend x (S.Interval (I.flip i)) env) (diff x e)) in
      let yl = I.lower y in
      let dl = I.lower d in
      match D.sgn dl with
  	| `negative ->
  	    let a' = D.sub ~prec ~round:D.up a (D.div ~prec ~round:D.down yl dl) in
  	      R.intersection
  		(R.of_interval i)
  		(R.closed_right_ray a')
  	| `zero ->
  	    (match D.sgn yl with
  	       | `negative | `zero -> R.of_interval i
  	       | `positive -> R.empty)
  	| `positive ->
  	    let b' = D.sub ~prec ~round:D.down a (D.div ~prec ~round:D.up yl dl) in
  	      R.intersection
  		(R.of_interval i)
  		(R.closed_left_ray b')
  (* The function [estimate prec env i x p] returns a pair of sets [(a,b)]
     such that in environment [env] the proposition [p] with free
     variable [x] ranging over interval [i] fails everywhere on [a] and
     holds everywhere on [b].
  *)
  
  let rec estimate_true k prec env x i = function
    | S.True -> R.of_interval i
    | S.False -> R.empty
    | S.And lst ->
        List.fold_left
  	(fun r p -> R.intersection r (estimate_true k prec env x i p))
  	R.real_line
  	lst
    | S.Or lst ->
        List.fold_left
  	(fun r p -> R.union r (estimate_true k prec env x i p))
  	R.empty
  	lst
    | S.Less (e1, e2) -> estimate_positive prec env x i (S.Binary (S.Minus, e2, e1))
    | S.Exists (y, j, p) ->
        estimate_true k prec (Env.extend y (S.Dyadic (I.midpoint prec k j)) env) x i p
    | S.Forall (y, j, p) ->
        estimate_true k prec (Env.extend y (S.Interval j) env) x i p
    | _ -> assert false
  
  let rec estimate_false k prec env x i = function
    | S.True -> R.empty
    | S.False -> R.of_interval i
    | S.And lst ->
        List.fold_left
  	(fun r p -> R.union r (estimate_false k prec env x i p))
  	R.empty
  	lst
    | S.Or lst ->
        List.fold_left
  	(fun r p -> R.intersection r (estimate_false k prec env x i p))
  	R.real_line
  	lst
   (* | S.Less (e1, e2) -> estimate_non_positive prec env x i (S.Binary (S.Minus, e2, e1))*)
    | S.Less (e1, e2) ->
       let r = estimate_non_positive k prec env x i (S.Binary (S.Minus, e2, e1)) in
   (*    print_endline ("Estimated " ^ S.string_of_name x ^ " on " ^ I.to_string i ^ " with " ^ Env.string_of_env env ^ " | " ^ S.string_of_expr (S.Less (e1, e2)) ^ " to be false on " ^ R.to_string r ^ "\n");*)
	r
    | S.Exists (y, j, p) ->
        estimate_false k prec (Env.extend y (S.Interval (I.flip j)) env) x i p
    | S.Forall (y, j, p) ->
        estimate_false k prec (Env.extend y (S.Dyadic (I.midpoint prec k j)) env) x i p
    | _ -> assert false
  
  let estimate k prec env x i p =
    (estimate_false k prec env x i p, estimate_true k prec env x i p)
  
end;;
 
