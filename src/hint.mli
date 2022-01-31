open Utils

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
type rw_hint = { 
  name : string; 
  rule : Rewrite.rw_erule;
}

val pp_rw_hint : Format.formatter -> rw_hint -> unit

(*------------------------------------------------------------------*)
type rewrite_db = rw_hint list Match.Hm.t

val pp_rewrite_db : Format.formatter -> rewrite_db -> unit

(*------------------------------------------------------------------*)
type hint_db

val empty_hint_db : hint_db 

val get_rewrite_db : hint_db -> rewrite_db

(*------------------------------------------------------------------*)
type p_hint =
  | Hint_rewrite of lsymb

val add_hint_rewrite : 
  lsymb -> Type.tvars -> Term.term -> hint_db -> hint_db
