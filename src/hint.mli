type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
type rewrite_db = (string * Rewrite.rw_erule) list

(*------------------------------------------------------------------*)
type hint_db

val empty_hint_db : hint_db 

val get_rewrite_db : hint_db -> rewrite_db
val get_smt_db     : hint_db -> Term.message list

(*------------------------------------------------------------------*)
type p_hint =
  | Hint_rewrite of lsymb
  | Hint_smt     of lsymb

val add_hint_rewrite : 
  lsymb -> Type.tvars -> Term.message -> hint_db -> hint_db

val add_hint_smt : Term.message -> hint_db -> hint_db
