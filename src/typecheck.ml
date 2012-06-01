(* \section{Type checking (module [Typecheck])} *)

module Make = functor (D : Dyadic.DYADIC) ->
struct
  module I = Interval.Make(D)
  module S = Syntax.Make(D)
  open S

  let error = Message.typecheck_error

  let check_segment i =
    if not (I.forward i) then error "illegal interval"

  let check_compact_segment i =
    if not (I.proper i) then error "not a compact interval"

  (* [type_of ctx e] computes the type of expression [e] in context [ctx]. *)
  let rec type_of ctx = function
    | Var x ->
	(try
	   List.assoc x ctx
	 with Not_found -> error ("Unknown variable " ^ string_of_name x))
    | RealVar (x, _) ->
	error ("Typechecking encountered areal variable " ^ string_of_name x ^
		 ". This should not happen")
    | Dyadic _ -> Ty_Real
    | Interval _ -> Ty_Real
    | Cut (x, i, p1, p2) ->
	check_segment i ;
	check ((x, Ty_Real)::ctx) Ty_Sigma p1 ;
	check ((x, Ty_Real)::ctx) Ty_Sigma p2 ;
	Ty_Real
    | Binary (_, e1, e2) ->
	check ctx Ty_Real e1 ;
	check ctx Ty_Real e2 ;
	Ty_Real
    | Unary (_, e) ->
	check ctx Ty_Real e ;
	Ty_Real
    | Power (e, k) ->
	check ctx Ty_Real e ;
	Ty_Real
    | True -> Ty_Sigma
    | False -> Ty_Sigma
    | And lst
    | Or lst  -> List.iter (check ctx Ty_Sigma) lst ; Ty_Sigma
    | Less (e1, e2) ->
	check ctx Ty_Real e1 ;
	check ctx Ty_Real e2 ;
	Ty_Sigma
    | Exists (x, s, p) ->
	check_segment s ;
	check ((x,Ty_Real)::ctx) Ty_Sigma p ;
	Ty_Sigma
    | Forall (x, s, p) ->
	check_compact_segment s ;
	check ((x,Ty_Real)::ctx) Ty_Sigma p ;
	Ty_Sigma
    | Let (x, e1, e2) ->
	let ty = type_of ctx e1 in
	  type_of ((x,ty)::ctx) e2
    | Tuple lst -> Ty_Tuple (List.map (type_of ctx) lst)
    | Proj (e, k) ->
	(match type_of ctx e with
	   | Ty_Tuple lst as ty ->
	       (try List.nth lst k with Failure "nth" ->
		  error ("Expected at least " ^ string_of_int k ^
			   " components but got " ^ string_of_type ty))
	   | ty -> error ("Expected a tuple but got " ^ string_of_type ty)
	)
    | Lambda (x, ty, e) ->
	Ty_Arrow (ty, type_of ((x,ty)::ctx) e)
    | App (e1, e2) ->
	(match type_of ctx e1 with
	   | Ty_Arrow (ty1, ty2) -> check ctx ty1 e2 ; ty2
	   | ty -> error ("Expected a function but got " ^ string_of_type ty))

  (* Does [e] have type [ty] in context [ctx]? *)
  and check ctx ty e =
    let ty' = type_of ctx e in 
      if ty <> ty' then
	error (string_of_type ty ^ " expected but got " ^ string_of_type ty')
end;;
