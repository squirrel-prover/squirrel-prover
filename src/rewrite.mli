(** A rewrite rule.
    Invariant: if
    [{ rw_tyvars = tyvars; rw_vars = sv; rw_conds = φ; rw_rw = (l,r); }]
    is a rewrite rule, then:
    - sv ⊆ FV(l)
    - ((FV(r) ∪ FV(φ)) ∩ sv) ⊆ FV(l) *)
type rw_rule = {
  rw_tyvars : Type.tvars;            (** type variables *)
  rw_vars   : Vars.Sv.t;             (** term variables *)
  rw_conds  : Term.term list;        (** premises *)
  rw_rw     : Term.term * Term.term; (** pair (source, destination) *)
}

val pp_rw_rule : Format.formatter -> rw_rule -> unit

(*------------------------------------------------------------------*)
val check_rule : rw_rule -> unit

val pat_to_rw_rule :
  ?loc:Location.t ->
  [< `LeftToRight | `RightToLeft ] ->
  Term.term Match.pat ->
  rw_rule

(*------------------------------------------------------------------*)
(** Try to do a rewrite at head position in a term.  *)
val rewrite_head :
  Symbols.table ->
  SystemExpr.t ->
  rw_rule ->
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
  rw_rule ->
  Equiv.any_form -> rw_res
