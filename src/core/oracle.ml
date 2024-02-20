include Symbols.Oracle

type Symbols.data += Oracle_data of Term.term

(*------------------------------------------------------------------*)
(** Return the oracle data associated to a symbol [s]. *)
let get_oracle (s : Symbols.fname) table : Term.term option = 
  let s = Symbols.Oracle.of_string s.np (Symbols.to_string s.s) in
  match Symbols.Oracle.get_data s table with
  | Oracle_data s -> Some s
  | _                           -> None
  | exception Not_found
  | exception Symbols.Error _   -> None

(*------------------------------------------------------------------*)
let add_oracle ((opt_name, v: Symbols.lsymb * Term.term)) table =
  let data = Oracle_data v in
  let table, _ = Symbols.Oracle.declare ~approx:false table opt_name ~data:data in
  table

(** From the name of the function, returns the corresponding formula. If no tag
   formula was defined, returns False. *)
(* val get_oracle_tag_formula : string -> Symbols.table  -> Term.term *)
let get_oracle_tag_formula h table =
  try match get_oracle h table with
  | Some f -> f
  | None -> Term.mk_false
  with Symbols.Error _ -> Term.mk_false (* if symbol error it's just
                                           that it didn't find it *)

