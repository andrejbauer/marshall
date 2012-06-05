(** Common definitions. *)

(** Positions *)
type position =
  | Position of Lexing.position * Lexing.position (** delimited position *)
  | Nowhere (** unknown region *)

(** A type enriched with a position *)
type 'a pos = 'a * position

(** A union of two positions *)
let join_pos (_, pos1) (_, pos2) =
  match pos1, pos2 with
  | _, Nowhere | Nowhere, _ -> Nowhere
  | Position (b1, _), Position (_, e2) -> Position (b1, e2)

(** Variants of association list operations that map into [option] type instead
    of raising [Not_found] *)
let lookup k env =
  try
    Some (List.assoc k env)
  with
    | Not_found -> None

let find p lst =
  try
    Some (List.find p lst)
  with
    | Not_found -> None
