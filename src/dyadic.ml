module type DYADIC =
sig
  type t
  type rounding_mode

  val down : rounding_mode
  val up : rounding_mode
  val anti : rounding_mode -> rounding_mode
  val of_int : ?prec:int -> round:rounding_mode -> int -> t
  val make_int : ?prec:int -> round:rounding_mode -> int -> int -> t
  val zero : t
  val one : t
  val negative_one : t
  val two : t
  val half : prec:int -> round:rounding_mode -> t
  val cmp : t -> t -> [> `equal | `greater | `less ]
  val min : t -> t -> t
  val max : t -> t -> t
  val sgn : t -> [> `negative | `positive | `zero ]
  val lt : t -> t -> bool
  val gt : t -> t -> bool
  val eq : t -> t -> bool
  val leq : t -> t -> bool
  val geq : t -> t -> bool
  val is_zero : t -> bool
  val negative : t -> bool
  val positive : t -> bool
  val nonpositive : t -> bool
  val nonnegative : t -> bool
  val positive_infinity : t
  val negative_infinity : t
  val is_infinity : t -> bool
  val is_positive_infinity : t -> bool
  val is_negative_infinity : t -> bool
  val is_number : t -> bool
  val is_nan : t -> bool
  val classify : t -> [`nan | `negative_infinity | `number | `positive_infinity ]
  val add : ?prec:int -> round:rounding_mode -> t -> t -> t
  val sub : ?prec:int -> round:rounding_mode -> t -> t -> t
  val neg : ?prec:int -> round:rounding_mode -> t -> t
  val mul : ?prec:int -> round:rounding_mode -> t -> t -> t
  val pow : ?prec:int -> round:rounding_mode -> t -> int -> t
  val div : prec:int -> round:rounding_mode -> t -> t -> t
  (*val exp : prec:int -> round:rounding_mode -> t -> t*)
  val inv : prec:int -> round:rounding_mode -> t -> t
  val shift : ?prec:int -> round:rounding_mode -> t -> int -> t
  val halve : ?prec:int -> round:rounding_mode -> t -> t
  val double : ?prec:int -> round:rounding_mode -> t -> t
  val average : t -> t -> t
  val of_string : string -> t
  val to_string : t -> string
  val get_exp : t -> int
end;;
