(* \section{Runtime envoronments (module [Environment])} *)

(* An environment is an associative list mapping variable names to
   expressions. *)

module Make = functor (D : Dyadic.DYADIC) ->
struct
  module S = Syntax.Make(D)
    
  type environment = (S.name * S.expr) list
      
  (* Get [x] in environment [env]. *)
  let get x env =
    try
      List.assoc x env
    with
	Not_found -> Message.runtime_error ("Unknown variable " ^ S.string_of_name x)
	  
  (* Extend [env] with [(x,e)]. *)
  let extend x e env = (x,e) :: env
    
end


