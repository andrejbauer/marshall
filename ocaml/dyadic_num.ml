(* \section{Dyadic numbers with [Num] (module [Dyadic_num])} *)

(* Dyadic numbers with the Ocaml [Num] package. This is a lot slower
   than [Dyadic_mpfr] but is independent of any third-party libraries.   

   The [Dyadic_mpfr] package measures output preceision with bits of
   mantissa [prec], and uses rounding modes. This makes less sense
   with [Dyadic_num] because the OCaml package [Num] does not support
   any bit manipulation operations (except for the semi-documented
   [Nat] module--someone should implement proper dyadics directly on
   top of [Nat], that would be helpful. See the enclosed document
   RT-0141.ps for documentation on [Nat]). So we fake output precision
   by computing exact results which are then truncated and rounded
   with the [normalize] function.
*)

open Ratio

type t =
  | NegativeInfinity
  | Ratio of ratio 
  | PositiveInfinity
  | NaN

(* \subsection{Rounding modes} *)

type rounding_mode = Down | Up

let down = Down

let up = Up

(* Invert the rounding mode.*)
let anti = function
  | Down -> Up
  | Up -> Down

(* \subsection{Constructors} *)

(* XXX: Not finished, should make numerator smaller. *)
let normalize (prec:int) (round:rounding_mode) m = m

let of_int ?prec ?round k = Ratio (ratio_of_int k)

(* Big integer of type [Big_int] to dyadic. *)
let of_integer ~prec ~round k = Ratio (ratio_of_big_int k)

let pow2 e = Big_int.power_int_positive_int 2 e
  
let make ~prec ~round m e =
  if e >= 0 then
    of_integer ~prec:prec ~round:round (Big_int.mult_big_int m (pow2 e))
  else Ratio (create_ratio m (pow2 (-e)))

let make_int ~prec ~round m e =
  make ~prec:prec ~round:round (Big_int.big_int_of_int m) e

(* \subsection{Constants} *)

let zero = of_int 0

let one = of_int 1

let negative_one = of_int (-1)

let two = of_int 2

let half = make_int 1 (-1)

(* \subsection{Order} *)

let nan_exc = Invalid_argument "Dyadic_num: nan encountered"

let cmp a b =
  match a, b with
    | (NaN, _) | (_, NaN) -> raise nan_exc
    | NegativeInfinity, NegativeInfinity -> `equal
    | NegativeInfinity, (Ratio _ | PositiveInfinity) -> `less
    | Ratio _, NegativeInfinity -> `greater
    | Ratio a, Ratio b -> 
	let c = compare_ratio a b in
	  if c < 0 then `less
	  else if c > 0 then `greater
	  else `equal
    | Ratio _, PositiveInfinity -> `less
    | PositiveInfinity, (NegativeInfinity | Ratio _) -> `greater
    | PositiveInfinity, PositiveInfinity -> `equal

let min a b = 
  match a, b with
    | NaN, _ | _, NaN -> raise nan_exc
    | NegativeInfinity, _
    | _, NegativeInfinity -> NegativeInfinity
    | PositiveInfinity, a
    | a, PositiveInfinity -> a
    | Ratio a, Ratio b -> Ratio (min_ratio a b)

let max a b =
  match a, b with
    | NaN, _ | _, NaN -> raise nan_exc
    | NegativeInfinity, a
    | a, NegativeInfinity -> a
    | _, PositiveInfinity
    | PositiveInfinity, _ -> PositiveInfinity
    | Ratio a, Ratio b -> Ratio (max_ratio a b)

let sgn = function
  | NaN -> raise nan_exc
  | NegativeInfinity -> `negative
  | PositiveInfinity -> `positive
  | Ratio a ->
      let s = sign_ratio a in
	if s < 0 then `negative
	else if s > 0 then `positive
	else `zero

(* less *)
let lt a b = (cmp a b = `less)

(* greater *)
let gt a b = (cmp a b = `greater)

(* equal *)
let eq a b = (cmp a b = `equal)

(* less or equal *)
let leq a b = (cmp a b <> `greater)

(* greater or equal *)
let geq a b = (cmp a b <> `less)

let is_zero a = (sgn a = `zero)

let negative a = (sgn a = `negative)

let positive a = (sgn a = `positive)

let nonpositive a = (sgn a <> `positive)

let nonnegative a = (sgn a <> `negative)

(* \subsection{Special values} *)

let positive_infinity = PositiveInfinity

let negative_infinity = NegativeInfinity

(* Depending on the rounding mode, return negative or positive infinity *)
let infinity = function
  | Down -> negative_infinity
  | Up -> positive_infinity

let is_infinity = function
  | NegativeInfinity | PositiveInfinity -> true
  | Ratio _ -> false
  | NaN -> false

let is_positive_infinity a = (a = PositiveInfinity)

let is_negative_infinity a = (a = NegativeInfinity)

let is_number = function
  | Ratio _ -> true
  | PositiveInfinity | NegativeInfinity | NaN -> false

let is_nan a = (a = NaN)

let classify = function
  | NegativeInfinity -> `negative_infinity
  | Ratio _ -> `number
  | PositiveInfinity -> `positive_infinity
  | NaN -> `nan

(* \subsection{Arithmetic} *)  

(* Arithmetic operations need to take care of infinite operands when
   the result would be [nan] (not a number). *)

(* Addition. *)
let add ~prec ~round a b =
  match a, b with
    | (NaN, _) | (_, NaN) -> infinity round
    | NegativeInfinity, NegativeInfinity -> NegativeInfinity
    | NegativeInfinity, Ratio _ -> NegativeInfinity
    | NegativeInfinity, PositiveInfinity -> infinity round
    | Ratio _, NegativeInfinity -> NegativeInfinity
    | Ratio a, Ratio b -> Ratio (normalize prec round (add_ratio a b))
    | Ratio _, PositiveInfinity -> PositiveInfinity
    | PositiveInfinity, NegativeInfinity -> infinity round
    | PositiveInfinity, Ratio _ -> PositiveInfinity
    | PositiveInfinity, PositiveInfinity -> PositiveInfinity

(* Subtraction. *)
let sub ~prec ~round a b =
  match a, b with
    | NaN, _ | _, NaN -> infinity round
    | NegativeInfinity, NegativeInfinity -> infinity round
    | NegativeInfinity, Ratio _ -> NegativeInfinity
    | NegativeInfinity, PositiveInfinity -> NegativeInfinity
    | Ratio _, NegativeInfinity -> PositiveInfinity
    | Ratio a, Ratio b -> Ratio (normalize prec round (sub_ratio a b))
    | Ratio _, PositiveInfinity -> NegativeInfinity
    | PositiveInfinity, NegativeInfinity -> PositiveInfinity
    | PositiveInfinity, Ratio _ -> PositiveInfinity
    | PositiveInfinity, PositiveInfinity -> infinity round

(* Negation. *)
let neg ~prec ~round = function
  | NaN -> infinity round
  | NegativeInfinity -> PositiveInfinity
  | Ratio a -> Ratio (minus_ratio a)
  | PositiveInfinity -> NegativeInfinity

(* Multiplication. Special cases: $\pm\infty \times 0$ and $0 \times
   \pm\infty$. *)
let mul ~prec ~round a b =
  match a, b with
    | NaN, _ | _, NaN -> infinity round
    | NegativeInfinity, NegativeInfinity -> PositiveInfinity
    | NegativeInfinity, Ratio a
    | Ratio a, NegativeInfinity ->
	(let s = sign_ratio a in
	   if s < 0 then PositiveInfinity
	   else if s > 0 then NegativeInfinity
	   else infinity round)
    | NegativeInfinity, PositiveInfinity
    | PositiveInfinity, NegativeInfinity -> NegativeInfinity
    | Ratio a, Ratio b -> Ratio (normalize prec round (mult_ratio a b))
    | Ratio a, PositiveInfinity
    | PositiveInfinity, Ratio a ->
	(let s = sign_ratio a in
	   if s < 0 then NegativeInfinity
	   else if s > 0 then PositiveInfinity
	   else infinity round)
    | PositiveInfinity, PositiveInfinity -> PositiveInfinity

(* Powers with non-negative exponents. *)
let pow ~prec ~round a k =
  match a with
    | NaN -> infinity round
    | NegativeInfinity ->
	if k mod 2 = 0 then PositiveInfinity else NegativeInfinity
    | Ratio a -> Ratio (normalize prec round (power_ratio_positive_int a k))
    | PositiveInfinity -> PositiveInfinity

(* Division. *)
let div ~prec ~round a b =
  match a, b with
    | (NaN,_) | (_, NaN)
    | _, (NegativeInfinity | PositiveInfinity) -> infinity round
    | NegativeInfinity, Ratio a ->
	(let s = sign_ratio a in
	   if s < 0 then PositiveInfinity
	   else if s > 0 then NegativeInfinity
	   else infinity round)
    | Ratio a, Ratio b -> 
	if sign_ratio b = 0 then
	  infinity round
	else
	  Ratio (normalize prec round (div_ratio a b))
    | PositiveInfinity, Ratio a ->
	(let s = sign_ratio a in
	   if s < 0 then NegativeInfinity
	   else if s > 0 then PositiveInfinity
	   else infinity round)

(* Inverse. *)
let inv ~prec ~round = function
  | NaN
  | NegativeInfinity
  | PositiveInfinity -> infinity round
  | Ratio a ->
      if sign_ratio a = 0 then
	infinity round
      else
	Ratio (normalize prec round (inverse_ratio a))

(* Shift by a power of two. *)
let shift ~prec ~round a k =
  match a with
    | NaN -> NaN
    | NegativeInfinity -> NegativeInfinity
    | PositiveInfinity -> PositiveInfinity
    | Ratio a ->
	Ratio (normalize prec round (
	  if k = 0 then a
	  else if k > 0 then
	    mult_big_int_ratio (Big_int.power_int_positive_int 2 k) a
	  else
	    let p = numerator_ratio a in
	    let q = denominator_ratio a in
	      create_ratio p (Big_int.mult_big_int
				q
				(Big_int.power_int_positive_int 2 (-k)))
	))

let halve ~prec ~round = function
  | NaN -> NaN
  | NegativeInfinity -> NegativeInfinity
  | PositiveInfinity -> PositiveInfinity
  | Ratio a -> Ratio (
      let p = numerator_ratio a in
      let q = numerator_ratio a in
	create_ratio p (Big_int.mult_int_big_int 2 q)
    )

let double ?prec ~round a =     
  let prec = (match prec with None -> 0 | Some p -> p) in
  match a with
     NaN -> NaN
    | NegativeInfinity -> NegativeInfinity
    | PositiveInfinity -> PositiveInfinity
    | Ratio a -> Ratio (normalize prec round (mult_int_ratio 2 a))

(* [average a b] returns a dyadic which is guaranteed to be strictly
   between [a] and [b], close to the average. This only works for
   finite [a] and [b].
*)
let average a b =
  match a, b with
    | NaN, _ | _, NaN -> NaN
    | NegativeInfinity, PositiveInfinity -> NaN
    | PositiveInfinity, NegativeInfinity -> NaN
    | PositiveInfinity, _ | _, PositiveInfinity -> PositiveInfinity
    | NegativeInfinity, _ | _, NegativeInfinity -> NegativeInfinity
    | Ratio a, Ratio b ->
	let c = add_ratio a b in
	let p = numerator_ratio c in
	let q = denominator_ratio c in
	  Ratio (create_ratio p (Big_int.mult_int_big_int 2 q))

(* \subsection{String conversions} *)

let of_string str = Ratio (ratio_of_string str)

let to_string = function
  | NaN -> "nan"
  | PositiveInfinity -> "inf"
  | NegativeInfinity -> "-inf"
  | Ratio a -> string_of_ratio a

let get_exp a = 0
