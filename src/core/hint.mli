type rw_hint = { 
  name : string; 
  rule : LowRewrite.rw_rule;
}

val pp_rw_hint : Format.formatter -> rw_hint -> unit

(*------------------------------------------------------------------*)
type rewrite_db = rw_hint list Term.Hm.t

val pp_rewrite_db : Format.formatter -> rewrite_db -> unit

(*------------------------------------------------------------------*)
val get_rewrite_db : Symbols.table -> rewrite_db
val get_smt_db     : Symbols.table -> Term.term list

(*------------------------------------------------------------------*)
type p_hint =
  | Hint_rewrite of Symbols.p_path
  | Hint_smt     of Symbols.p_path

val add_hint_rewrite : 
  Symbols.p_path -> Type.tvars -> Term.term -> Symbols.table -> Symbols.table

val add_hint_smt : Term.term -> Symbols.table -> Symbols.table
