(** A rewrite rule.
    Invariant: if
    [{ rw_tyvars = tyvars; rw_vars = sv; rw_conds = φ; rw_rw = (l,r); }]
    is a rewrite rule, then:
    - sv ⊆ FV(l)
    - ((FV(r) ∪ FV(φ)) ∩ sv) ⊆ FV(l) *)
type rw_erule = {
  rw_tyvars : Type.tvars;        (** type variables *)
  rw_vars   : Vars.Sv.t;         (** term variables *)
  rw_conds  : Term.message list; (** premisses *)
  rw_rw     : Term.esubst;       (** pair (source, destination) *)
}

(*------------------------------------------------------------------*)
val check_erule : rw_erule -> unit

val pat_to_rw_erule :
  ?loc:Location.t ->
  [< `LeftToRight | `RightToLeft ] ->
  Term.message Match.pat ->
  rw_erule

(*------------------------------------------------------------------*)
(** Try to do a rewrite at head position in a term.  *)
val rewrite_head :
  Symbols.table ->
  SystemExpr.t ->
  rw_erule ->
  'a Term.term ->
  ('a Term.term * Term.message list) option

(*------------------------------------------------------------------*)
type rw_res = [
  | `Result of Equiv.any_form * Term.message list
  | `NothingToRewrite
  | `MaxNestedRewriting
]

(*------------------------------------------------------------------*)
val rewrite :
  Symbols.table ->
  SystemExpr.t ->
  Vars.env ->
  TacticsArgs.rw_count ->
  rw_erule ->
  Equiv.any_form -> rw_res
