include Symbols.Oracle

type p_oracle_val =
  | Oracle_term of Term.term

type Symbols.data += Oracle_data of p_oracle_val

let def_of_oracle = function
  | Oracle_term _ -> Symbols.PTerm

let get_oracle (s:Symbols.lsymb) table : Term.term option = 
  let ns = Symbols.Oracle.of_lsymb s table in
  match Symbols.Oracle.get_data ns table with
  | Oracle_data (Oracle_term s) -> Some s
  | _ -> None

(*------------------------------------------------------------------*)
(** Oracle Options Management **)

exception Option_already_defined

(* add oracle def *)
(* val add_oracle : (string*Term.term) -> Symbols.table -> Symbols.table *)
let add_oracle ((opt_name,opt_val:Symbols.lsymb*Term.term)) table =
    (* to not overlap other symbol in map *)
    if Symbols.Oracle.mem_lsymb opt_name table then
      raise Option_already_defined
    else 
      let v = (Oracle_term opt_val) in
      let data = Oracle_data v in
      let table = fst (Symbols.Oracle.declare_exact table opt_name ~data:data
                         (def_of_oracle v)) in
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

