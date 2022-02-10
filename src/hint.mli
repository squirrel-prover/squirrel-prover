type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
type rewrite_db = (string * Rewrite.rw_erule) list

(*------------------------------------------------------------------*)
type hint_db

val empty_hint_db : hint_db 

val get_rewrite_db : hint_db -> rewrite_db

(*------------------------------------------------------------------*)
type p_hint =
  | Hint_rewrite of lsymb

val add_hint_rewrite : 
  lsymb -> Type.tvars -> Term.message -> hint_db -> hint_db
