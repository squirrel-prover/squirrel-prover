(** A rewrite rule is a tuple: 
    (type variables, term variables, premisses, left term, right term)
    Invariant: if (tyvars,sv,φ,l,r) is a rewrite rule, then
    - sv ⊆ FV(l)
    - ((FV(r) ∪ FV(φ)) ∩ sv) ⊆ FV(l) *)
type 'a rw_rule = 
  Type.tvars * Vars.Sv.t * Term.message list * 'a Term.term * 'a Term.term

type rw_erule = Type.tvars * Vars.Sv.t * Term.message list * Term.esubst

(*------------------------------------------------------------------*)
val check_erule : rw_erule -> unit

val pat_to_rw_erule : 
  ?loc:Location.t ->
  [< `LeftToRight | `RightToLeft ] ->
  Term.message Match.pat ->
  rw_erule

(*------------------------------------------------------------------*)
val rewrite_head : 
  Symbols.table ->
  SystemExpr.t -> 
  rw_erule -> 
  'a Term.term -> 
  ('a Term.term * Term.message list) option 
