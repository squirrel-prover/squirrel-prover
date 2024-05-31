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

