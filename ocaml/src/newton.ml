(* \subsection{Newton's method} *)

(* This section is not finished because we have to sort out problems which
   are caused by appearance of back-to-front intervals. *)

(* Does [x] occur freely in [e]? *)
let rec free x = function
  | Var y -> x <> y
  | RealVar (y, _) -> x <> y
  | Dyadic _
  | Interval _
  | True
  | False -> true
  | Cut (y, _, p1, p2) -> x = y || (free x p1 && free x p2)
  | Binary (_, e1, e2)
  | Less (e1, e2)
  | App (e1, e2)  -> free x e1 && free x e2
  | Unary (_, e)
  | Power (e, _)
  | Proj (e, _) -> free x e
  | And lst
  | Or lst
  | Tuple lst -> List.for_all (free x) lst
  | Lambda (y, _, e)
  | Exists (y, _, e)
  | Forall (y, _, e) -> x = y || free x e
  | Let (y, e1, e2) -> free x e1 && (x = y || free x e2)

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

let zero = Dyadic D.zero
let one = Dyadic D.one

let rec diff x = function
  | Var y -> if x = y then one else zero
  | RealVar (y, _) -> if x = y then one else zero
  | Dyadic _ -> zero
  | Interval _ -> zero
  | Cut (y, i, p1, p2) -> 
      if x = y || (free x p1 && free x p2) then
	zero
      else
	Interval I.bottom
  | Binary (Plus, e1, e2) -> Binary (Plus, diff x e1, diff x e2)
  | Binary (Minus, e1, e2) -> Binary (Minus, diff x e1, diff x e2)
  | Binary (Times, e1, e2) -> 
      Binary (Plus,
	      Binary (Times, diff x e1, e2),
	      Binary (Times, e1, diff x e2))
  | Binary (Quotient, e1, e2) ->
      Binary (Quotient,
	      Binary (Minus,
		      Binary (Times, diff x e1, e2),
		      Binary (Times, e1, diff x e2)),
	      Power (e2, 2))
  | Unary (Opposite, e) -> Unary (Opposite, diff x e)
  | Unary (Inverse, e) -> Binary (Quotient, diff x e, Power (e, 2))
  | Unary (Exp, e) -> Binary (Times, Unary (Exp, e), diff x e)
  | Power (e, 0) -> zero
  | Power (e, 1) -> diff x e
  | Power (e, k) ->
      Binary (Times,
	      Dyadic (D.of_int k),
	      Binary (Times,
		      Power (e, k-1),
		      diff x e))
  | True
  | False
  | Less _
  | And _
  | Or _
  | Exists _
  | Forall _ -> error "Cannot differentiate a proposition"
  | Let (y, e1, e2) -> error "Cannot differentiate a local definition"
  | Tuple _ -> failwith "Cannot differentiate a tuple"
  | Proj (_, _) -> failwith "Cannot differentiate a projection"
  | Lambda (x, ty, e) -> failwith "Cannot differentiate an abstraction"
  | App (e1, e2) -> failwith "Cannot differentiate a redex"

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
    Region.empty
  else
    let a = I.lower i in
    let y = get_interval (lower prec (extend x (Dyadic a) env) e) in
    let d = get_interval (lower prec (extend x (Interval i) env) (diff x e)) in
    let yl = I.lower y in
    let dl = I.lower d in
      match D.sgn dl with
	| `negative ->
	    let b' = D.sub prec D.down a (D.div prec D.up yl dl) in
	      Region.intersection
		(Region.of_interval i)
		(Region.open_left_ray b')
	| `zero ->
	    (match D.sgn yl with
	       | `negative | `zero -> Region.empty
	       | `positive -> Region.of_interval i)
	| `positive ->
	    let a' = D.sub prec D.up a (D.div prec D.down yl dl) in
	      Region.intersection
		(Region.of_interval i)
		(Region.open_right_ray a')

(* The function [estimate_non_positive env i x e] returns a
   set such that in environment [env] the expression [e] with
   free variable [x] ranging over interval [i] is guaranteed to be
   non-positive everywhere on the set.
*)

let estimate_non_positive prec env x i e =
  (* For infinite intervals we give up. We could try to do something
     more intelligent, such as computing the derivative at infinity
     (using a suitable transformation which moves infinity to a finite
     point). *)
  if not (I.proper i) then
    Region.empty
  else
    let a = I.lower i in
    let y = get_interval (upper prec (extend x (Dyadic a) env) e) in
    let d = get_interval (lower prec (extend x (Interval i) env) (diff x e)) in
    let yu = I.lower y in
    let du = I.upper d in
      match D.sgn du with
	| `negative ->
	    let a' = D.sub prec D.up a (D.div prec D.down yu du) in
	      Region.intersection
		(Region.of_interval i)
		(Region.closed_right_ray a')
	| `zero ->
	    (match D.sgn yu with
	       | `negative | `zero -> Region.of_interval i
	       | `positive -> Region.empty)
	| `positive ->
	    let b' = D.sub prec D.down a (D.div prec D.up yu du) in
	      Region.intersection
		(Region.of_interval i)
		(Region.closed_left_ray b')

(* The function [estimate prec env i x p] returns a pair of sets [(a,b)]
   such that in environment [env] the proposition [p] with free
   variable [x] ranging over interval [i] fails everywhere on [a] and
   holds everywhere on [b].
*)

let rec estimate_true k prec env x i = function
  | True -> Region.of_interval i
  | False -> Region.empty
  | And lst ->
      List.fold_left
	(fun r p -> Region.intersection r (estimate_true k prec env x i p))
	Region.real_line
	lst
  | Or lst ->
      List.fold_left
	(fun r p -> Region.union r (estimate_true k prec env x i p))
	Region.empty
	lst
  | Less (e1, e2) -> estimate_positive prec env x i (Binary (Minus, e2, e1))
  | Exists (y, j, p) ->
      estimate_true k prec (extend y (Dyadic (I.midpoint prec k j)) env) x i p
  | Forall (y, j, p) ->
      estimate_true k prec (extend y (Interval j) env) x i p
  | _ -> assert false

let rec estimate_false k prec env x i = function
  | True -> Region.empty
  | False -> Region.of_interval i
  | And lst ->
      List.fold_left
	(fun r p -> Region.union r (estimate_false k prec env x i p))
	Region.empty
	lst
  | Or lst ->
      List.fold_left
	(fun r p -> Region.intersection r (estimate_false k prec env x i p))
	Region.real_line
	lst
  | Less (e1, e2) ->
      let r = estimate_non_positive prec env x i (Binary (Minus, e2, e1)) in
	print_endline ("Estimated " ^ string_of_name x ^ " on " ^ I.to_string i ^ " with " ^ string_of_env env ^ " | " ^ string_of_expr (Less (e1, e2)) ^ " to be false on " ^ Region.to_string r) ;
		       r
  | Exists (y, j, p) ->
      estimate_false k prec (extend y (Interval (I.flip j)) env) x i p
  | Forall (y, j, p) ->
      estimate_false k prec (extend y (Dyadic (I.midpoint prec k j)) env) x i p
  | _ -> assert false

let estimate k prec env x i p =
  (estimate_false k prec env x i p, estimate_true k prec env x i p)
      
