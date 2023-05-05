(** Rewriting types and functions which do not depend on [Match] *)

(*------------------------------------------------------------------*)
module L   = Location
module SE  = SystemExpr

(*------------------------------------------------------------------*)
(** A rewrite rule.
    Invariant: if
    [{ rw_tyvars = tyvars; rw_vars = sv; rw_conds = φ; rw_rw = (l,r); }]
    is a rewrite rule, then:
    - sv ⊆ FV(l)
    - ((FV(r) ∪ FV(φ)) ∩ sv) ⊆ FV(l) *)
type rw_rule = {
  rw_tyvars : Type.tvars;            (** type variables *)
  rw_system : SE.t;                  (** systems the rule applies to *)
  rw_vars   : Vars.tagged_vars;      (** term variables *)
  rw_conds  : Term.term list;        (** premises *)
  rw_rw     : Term.term * Term.term; (** pair (source, destination) *)
}

val pp_rw_rule : Format.formatter -> rw_rule -> unit

(*------------------------------------------------------------------*)
val check_rule : rw_rule -> unit

val pat_to_rw_rule :
  ?loc:Location.t ->
  destr_eq  : (Term.term -> (Term.term * Term.term) option) ->
  destr_not : (Term.term -> (            Term.term) option) ->
  SE.t ->
  [< `LeftToRight | `RightToLeft ] ->
  Term.term Term.pat ->
  rw_rule
