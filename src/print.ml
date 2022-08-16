(* Fancy printing of expressions and errors.
   At the moment we just use the old routines for converting to strings. *)

let fprintf = Format.fprintf

let print ?(max_level=9999) ?(at_level=0) ppf =
  if max_level < at_level then
    begin
      Format.fprintf ppf "(@[";
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@])") ppf
    end
  else
    begin
      Format.fprintf ppf "@[";
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@]") ppf
    end

let position pos ppf =
  match pos with
  | Common.Nowhere ->
      Format.fprintf ppf "unknown position"
  | Common.Position (begin_pos, _) ->
      let begin_char = begin_pos.Lexing.pos_cnum - begin_pos.Lexing.pos_bol + 1 in
      let begin_line = begin_pos.Lexing.pos_lnum in
      let filename = begin_pos.Lexing.pos_fname in

      if String.length filename != 0 then
        Format.fprintf ppf "file %S, line %d, char %d" filename begin_line begin_char
      else
        Format.fprintf ppf "line %d, char %d" begin_line begin_char

let verbosity = ref 3
let message ?(pos=Common.Nowhere) msg_type v =
  if v <= !verbosity then
    begin
      Format.eprintf "@[%s (%t): " msg_type (position pos);
      Format.kfprintf (fun ppf -> fprintf ppf "@]@.") Format.err_formatter
    end
  else
    Format.ifprintf Format.err_formatter

let error (pos, err_type, msg) = message ~pos (err_type) 1 "%s" msg
let check ?pos = message ?pos "Check" 2
let warning ?pos = message ?pos "Warning" 3
let debug ?pos = message ?pos "Debug" 4
