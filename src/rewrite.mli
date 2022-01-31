(** A rewrite rule.
    Invariant: if
    [{ rw_tyvars = tyvars; rw_vars = sv; rw_conds = φ; rw_rw = (l,r); }]
    is a rewrite rule, then:
    - sv ⊆ FV(l)
    - ((FV(r) ∪ FV(φ)) ∩ sv) ⊆ FV(l) *)
type rw_erule = {
  rw_tyvars : Type.tvars;     (** type variables *)
  rw_vars   : Vars.Sv.t;      (** term variables *)
  rw_conds  : Term.term list; (** premisses *)
  rw_rw     : Term.esubst;    (** pair (source, destination) *)
}

val pp_rw_erule : Format.formatter -> rw_erule -> unit

(*------------------------------------------------------------------*)
val check_erule : rw_erule -> unit

val pat_to_rw_erule :
  ?loc:Location.t ->
  [< `LeftToRight | `RightToLeft ] ->
  Term.term Match.pat ->
  rw_erule

(*------------------------------------------------------------------*)
(** Try to do a rewrite at head position in a term.  *)
val rewrite_head :
  Symbols.table ->
  SystemExpr.t ->
  rw_erule ->
  Term.term ->
  (Term.term * Term.term list) option

(*------------------------------------------------------------------*)
type rw_res = [
  | `Result of Equiv.any_form * Term.term list
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
