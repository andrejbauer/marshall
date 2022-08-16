(** Abstract syntax of the Marshall language. *)

module Make = functor (D: Dyadic.DYADIC) ->
struct
  module I = Interval.Make(D)

  (** The type of variable names. Variables are either original or generated. *)
  type name =
    | Ident of string
    | Gensym of string * int

  (** Generate a fresh variable name. *)
  let fresh_name =
    let k = ref 0 in
      fun s -> incr k; Gensym (s,!k)

  (** Convert a name to a string. *)
  let string_of_name = function
    | Ident str -> str
    | Gensym (s,k) -> s ^ string_of_int k

  (** In Marshall we have base types for reals and propositions, product types and
      function types. Function types are a mirage because all $\lambda$-abstractions get
      $\beta$-reduced away. *)
  type ty =
    | Ty_Sigma (* [prop] *)
    | Ty_Real  (* [real] *)
    | Ty_Arrow of ty * ty (* [t1 -> t2] *)
    | Ty_Tuple of ty list (* [t1 * t2 * ... * tn] *)

  (** Binary arithmetical operations. *)
  type binary =
    | Plus
    | Minus
    | Times
    | Quotient

  (** Convert a binary operation to its string representation. *)
  let string_of_binary = function
    | Plus -> "+"
    | Minus -> "-"
    | Times -> "*"
    | Quotient -> "/"

  (** Operator precedences, used by [string_of_expr] below. *)
  let precs_of_binary = function
    | Times -> 50, 49, 50
    | Quotient -> 50, 49, 50
    | Plus -> 40, 39, 40
    | Minus -> 40, 39, 40

  (** Unary arithmetical operations. *)
  type unary =
    | Opposite
    | Inverse

  (** Convert a unary operation to its string representation. *)
  let string_of_unary = function
    | Opposite -> "-"
    | Inverse -> "inv"

  (** The abstract syntax of Marshall terms. *)
  type expr =
    | Var of name (* variable *)
    | RealVar of name * I.t (* real variable with a given range, see [Eval.refine] *)
    | Dyadic of D.t (* dyadic constant, syntax as in MPFR (subsumes floating-point) *)
    | Interval of I.t (* interval constant, no concrete syntax *)
    | Cut of name * I.t * expr * expr
	(* [Cut (x, [a, b], l, u)] is the real number in interval
	   $[a,b]$ whose lower cut is $\lambda x, l$ and upper cut is
	   $\lambda x, u$. There are three kinds of concrete syntax:
	   \begin{itemize}
	   \item [cut x left l right u]
	   \item [cut x : real left l right u]
	   \item [cut x : [a,b] left l right u]
	   \end{itemize} *)
    | Binary of binary * expr * expr
    | Unary of unary * expr
    | Power of expr * int (* Power by a natural constant *)
    | True
    | False
    | Less of expr * expr
	(* Apart from [a < b], concrete syntax also has sugars [a > b]
	   and $a ={e}= b$, which means $-e < a - b < e$. *)
    | And of expr list (* [p1 /\ p2 /\ ... /\ pn] *)
    | Or of expr list (* [p1 \/ p2 \/ ... \/ pn] *)
    | Exists of name * I.t * expr (* [exists x : [a,b], p] *)
    | Forall of name * I.t * expr (* [forall x : [a,b], p] *)
    | Let of name * expr * expr (* [let x = e1 in e2] *)
    | Tuple of expr list (* [(e1, ..., en)] *)
    | Proj of expr * int (* Concrete syntax for $k$-th projection is [e#k] *)
    | Lambda of name * ty * expr (* Concrete syntax is [fun x : ty => e] *)
    | App of expr * expr

  (** Toplevel commands *)
  type toplevel_cmd =
    | Expr of expr * bool       (* Expression, should it be traced? *)
    | Use of string             (* Include file [$use "<filename>"] *)
    | Definition of name * expr (* Top-level definition [let x = e] *)
    | Precision of D.t          (* Target precision [$precision d] *)
    | Hnf of expr               (* Compute head-normal form *)
    | Help                      (* Print help *)
    | Quit                      (* Exit toplevel [$quit] *)

  (** Convert a type to a string *)
  let string_of_type ty =
    let rec to_str n ty =
      let (m, str) =
	match ty with
	  | Ty_Sigma            -> (3, "prop")
	  | Ty_Real             -> (3, "real")
	  | Ty_Tuple lst        -> (2, String.concat "*" (List.map (to_str 2) lst))
	  | Ty_Arrow (ty1, ty2) -> (1, to_str 1 ty1 ^ " -> " ^ to_str 0 ty2)
      in
	if m > n then str else "(" ^ str ^ ")"
    in
      to_str (-1) ty

  (** Convert a expression to string *)
  let string_of_expr e =
    let rec to_str n e =
      let (m, str) =
	match e with
	  | Var x   ->           (100, string_of_name x)
	  | RealVar (x, i) ->    (100, "(" ^ string_of_name x ^ ":" ^ I.to_string i ^ ")")
	  | Dyadic q ->          (100, D.to_string q)
	  | Interval i ->        (100, I.to_string_number i)
	  | True | And [] ->     (100, "True")
	  | False | Or [] ->     (100, "False")
	  | Tuple lst ->         (100, "(" ^ (String.concat ", " (List.map (to_str 10) lst)) ^ ")")
	  | Proj (e, k) ->       (90, to_str 90 e ^ "#" ^ string_of_int k)
	  | App (e1, e2) ->      (85, to_str 84 e1 ^ " " ^ to_str 85 e2)
	  | Power (e, k) ->      (83, to_str 82 e ^ " ^ " ^ string_of_int k)
	  | Unary (op, e) ->     (80, string_of_unary op ^ " " ^ to_str 80 e)
	  | Binary (op, e1, e2) ->
	      let p, p1, p2 = precs_of_binary op in
		(p, to_str p1 e1 ^ " " ^ string_of_binary op ^ " " ^ to_str p2 e2)
	  | Less (e1, e2) ->     (30, to_str 30 e1 ^ " < " ^ to_str 30 e2)
	  | And lst ->           (20, String.concat " /\\ " (List.map (to_str 19) lst))
	  | Or lst ->            (15, String.concat " \\/ " (List.map (to_str 14) lst))
	  | Exists (x, t, p) ->  (10, "exists " ^ string_of_name x ^ " : " ^
				    I.to_string t ^ " , " ^ to_str 9 p)
	  | Forall (x, t, p) ->  (10, "forall " ^ string_of_name x ^ " : " ^
				    I.to_string t ^ " , " ^ to_str 9 p)
	  | Let (x, e1, e2)  ->  (10, "let " ^ string_of_name x ^ " = " ^ to_str 10 e1 ^
				    " in " ^ to_str 9 e2)
	  | Lambda (x, t, e) ->  (10, "fun " ^ string_of_name x ^ " : " ^ string_of_type t ^
				    " => " ^ to_str 9 e)
	  | Cut (x, i, p1, p2) -> (5, "cut " ^ string_of_name x ^ " : " ^
				     I.to_string i ^
				     " left " ^ to_str 5 p1 ^ " right " ^ to_str 5 p2)
      in
	if m > n then str else "(" ^ str ^ ")"
    in
      to_str (-1) e
end
