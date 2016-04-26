module Make = functor (D : Dyadic.DYADIC) ->
struct

  module I = Interval.Make(D)
  module Env = Environment.Make(D)
  module S = Syntax.Make(D)
  module N = Newton.Make(D)
  module R = Region.Make(D)
  module A = Approximate.Make(D)

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

    let rec free_in y e = match e with
	| S.Var x -> x = y
	| S.RealVar _ | S.Dyadic _ | S.Interval _ | S.True | S.False -> false
	| S.Cut (x, i, p1, p2) -> x<>y && (free_in y p1 || free_in y p2)
	| S.Binary (op, e1, e2) -> free_in y e1 || free_in y e2
	| S.Unary (op, e) -> free_in y e 
	| S.Power (e, k) -> free_in y e
	| S.Proj (e, k) ->
	    (match  e with
	       | S.Tuple _ as e' -> free_in y (A.proj e' k)
	       | e' -> free_in y e)
	| S.Less (e1, e2) -> free_in y e1 || free_in y e2
	| S.And lst -> List.fold_left (fun p e -> p || free_in y e) false lst
	| S.Or lst -> List.fold_left (fun p e -> p || free_in y e) false lst
	| S.Tuple lst -> List.fold_left (fun p e -> p || free_in y e) false lst
	| S.Lambda (x, ty, e) -> x<>y && (free_in y e)
	| S.Exists (x, i, e) -> x<>y && (free_in y e)
	| S.Forall (x, i, e) -> x<>y && (free_in y e)
	| S.App (e1, e2)  -> free_in y e1 || free_in y e2
	| S.Let (x, e1, e2) -> free_in y e1 || (x<>y && free_in y e2)

    let rec free_in_env x env e =
      match env with
	| [] -> false
	| (y,e')::l -> (if free_in y e then free_in x e' else false) || free_in_env x l e

  (* The first step of evaluation is to evaluate to head-normal form
     because we want to get rid of local definitions and redexes. This
     causes a huge inefficiency because it may unnecessarily multiply
     repeat subexpressions, but computation of derivatives cannot handle
     general applications and local definitions. *)

  let rec hnf ?(free=false) env e =        
    let alpha1 x env e =
      if free_in_env x env e then 
	let x' = S.fresh_name (S.string_of_name x) in
	  x', hnf ~free:true (Env.extend x (S.Var x') []) e
      else
	 x, e
    in      
    let alpha2 x env e1 e2 =
      if free_in_env x env e1 || free_in_env x env e2 then 
	let x' = S.fresh_name (S.string_of_name x) in
	  x', hnf ~free:true (Env.extend x (S.Var x') []) e1, hnf ~free:true (Env.extend x (S.Var x') []) e2
      else
	 x, e1, e2
    in      
    let hnf = hnf ~free in
      match e with
	| S.Var x ->
	    (try
	       List.assoc x env
	     with Not_found ->
	       if free then S.Var x else error ("Unknown variable " ^ S.string_of_name x))
	| (S.RealVar _ | S.Dyadic _ | S.Interval _ | S.True | S.False) as e -> e
	| S.Cut (x, i, p1, p2) ->
	    let x', p1', p2' = alpha2 x env p1 p2 in
	    let env' = Env.extend x' (S.Var x') env in		  
	      S.Cut (x', i, hnf env' p1', hnf env' p2')
	| S.Binary (op, e1, e2) -> S.Binary (op, hnf env e1, hnf env e2)
	| S.Unary (op, e) -> S.Unary (op, hnf env e)
	| S.Power (e, k) -> S.Power (hnf env e, k)
	| S.Proj (e, k) -> 
	    (match hnf env e with
	       | S.Tuple _ as e' -> A.proj e' k
	       | e' -> S.Proj (e', k))
	| S.Less (e1, e2) -> S.Less (hnf env e1, hnf env e2)
	| S.And lst -> S.And (List.map (hnf env) lst)
	| S.Or lst -> S.Or (List.map (hnf env) lst)
	| S.Tuple lst -> S.Tuple (List.map (hnf env) lst)
	| S.Lambda (x, ty, e) -> 
	  let x',e' = alpha1 x env e in 
	    S.Lambda (x', ty, hnf (Env.extend x' (S.Var x') env) e')
	| S.Exists (x, i, e) ->
	  let x',e' = alpha1 x env e in 
	    S.Exists (x', i, hnf (Env.extend x' (S.Var x') env) e')
	| S.Forall (x, i, e) -> 
	  let x',e' = alpha1 x env e in 
	    S.Forall (x', i, hnf (Env.extend x' (S.Var x') env) e')
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
      if A.lower prec env e = S.True then S.True
      else if A.upper prec env e = S.False then S.False
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
	      let a' = (if A.lower prec (Env.extend x (S.Dyadic m1) env) p1 = S.True then m1 else a) in
	      let b' = (if A.lower prec (Env.extend x (S.Dyadic m2) env) p2 = S.True then m2 else b) in
	    	
	      let j = I.make a' b' in
	      	(* Newton's method *)
	      let (r1, r2) = N.estimate k prec env x j p1 in
	      let (s1, s2) = N.estimate k prec env x j p2 in
      	      let a'' = D.max a' (D.max (R.supremum r2) (R.supremum s1)) in
	      let b'' = D.min b' (D.min (R.infimum  s2) (R.infimum r1)) in
	      match D.cmp a'' b'' with
		  | `less ->
		      (* The new interval *)
		    let l = I.make a'' b'' in	      	    
		    let env' = Env.extend x (S.RealVar (x, l)) env in
		    let q1 = refine k prec env' p1 in
		    let q2 = refine k prec env' p2 in
(*		    print_endline ("Cut: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (I.to_string j) ^ (I.to_string l) ^ (S.string_of_expr q1) ^ (S.string_of_expr q2));*)
		      S.Cut (x, l, q1, q2)
		  | `equal ->
		      (* We found an exact value *)
		    S.Dyadic a''
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
	  | S.And lst -> A.fold_and refn lst
	  | S.Or lst -> A.fold_or refn lst
	  | S.Exists (x, i, p) ->
	      let prec = make_prec prec i in
	      let q = refine k prec (Env.extend x (S.RealVar (x, i)) env) p in
	    (*  let (a1,b1) = N.estimate k prec env x i q in
              if R.is_inhabited b1 then S.True
              else
                (if R.is_inhabited a1 then
                  let lst = R.to_closed_intervals (R.closure (R.intersection (R.of_interval i) (R.complement a1))) in
		      A.fold_or (fun i -> make_exists x i q) lst
                else
		  let i1,i2 = I.split prec 1 i in  
	              A.fold_or (fun i -> make_exists x i q) [i1; i2])*)
	      let i1, i2 = I.split prec 1 i in
		(* Newton's method *)
	      let (a1, b1) = N.estimate k prec env x i1 q in

(*	      print_endline ("Exists: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (R.to_string a1) ^ (R.to_string b1));*)
	      if R.is_inhabited b1 then
		(* We could collect [b1] as a witness here. *)
		S.True
	      else
		let (a2, b2) = N.estimate k prec env x i2 q in
(*		  print_endline ("Exists: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (R.to_string a2) ^ (R.to_string b2));*)
		  if R.is_inhabited b2 then
		    (* We could collect [b2] as a witness here. *)
		    S.True
		  else
		    let lst1 = R.to_closed_intervals
		      (R.closure
			 (R.intersection
			    (R.of_interval i1)
			    (R.complement a1)))
		    in
		    let lst2 = R.to_closed_intervals
		      (R.closure
			 (R.intersection
			    (R.of_interval i2)
			    (R.complement a2)))
		    in
		      A.fold_or (fun i -> make_exists x i q) (lst1 @ lst2)
		
	      (*A.fold_or (fun i -> make_exists x i q) [i1; i2]*)

	  | S.Forall (x, i, p) ->
	      let prec = make_prec prec i in
	      let q = refine k prec (Env.extend x (S.RealVar (x, i)) env) p in
(*      let (a1, b1) = N.estimate k prec env x i q in
	      if R.is_inhabited a1 then
		(* We could take [a1] as witness for quantifier being false. *)
		S.False
	      else
                (if R.is_inhabited b1 then
 		    let lst = R.to_closed_intervals (R.closure (R.intersection (R.of_interval i) (R.complement b1))) in
		      A.fold_and (fun i -> make_forall x i q) lst
		else
	       	  let i1, i2 = I.split prec 1 i in
              	    A.fold_and (fun i -> make_forall x i q) [i1; i2])*)
	      
	       let i1, i2 = I.split prec 1 i in
		(* Newton's method *)
              let (a1, b1) = N.estimate k prec env x i1 q in
(*	      print_endline ("Forall: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (R.to_string a1) ^ (R.to_string b1));*)
	      if R.is_inhabited a1 then
		(* We could take [a1] as witness for quantifier being false. *)
		S.False
	      else
		let (a2, b2) = N.estimate k prec env x i2 q in
(*		print_endline ("Forall: " ^ (S.string_of_name x) ^ ":" ^ (I.to_string i) ^ ":" ^ (R.to_string a2) ^ (R.to_string b2));*)
		  if R.is_inhabited a2 then
		    (* We could take [a2] as witness for quantifier being false. *)
		    S.False
		  else
		    let lst1 = R.to_closed_intervals
		      (R.closure
			 (R.intersection
			    (R.of_interval i1)
			    (R.complement b1)))
		    in
		    let lst2 = R.to_closed_intervals
		      (R.closure
			 (R.intersection
			    (R.of_interval i2)
			    (R.complement b2)))
		    in
		      A.fold_and (fun i -> make_forall x i q) (lst1 @lst2)

              (*A.fold_and (fun i -> make_forall x i q) [i1; i2]*)
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

  (** [eval prec env e] evaluates expression [e] in environment [env] by
      repeatedly calling [refine]. It increases precision at each step,
      although we should do something more intelligent about that (not
      all subexpressions of [e] need the same precision). The argument
      [trace] determines whether debugging information should be printed
      out. *)
  let eval trace env e =
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
	    (match A.lower p env e with
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
      loop 1 32 (hnf env e)
end;;

