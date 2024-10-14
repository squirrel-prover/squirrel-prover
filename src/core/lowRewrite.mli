(** Rewriting types and functions which do not depend on [Match] *)

open Utils

(*------------------------------------------------------------------*)
module L   = Location
module SE  = SystemExpr

(*------------------------------------------------------------------*)
(** Local equalities can be rewritten only in local terms.
    Global equalities can be rewritten in local and global terms. *)
type rw_kind = LocalEq | GlobalEq

(*------------------------------------------------------------------*)
(** A rewrite rule.
    Invariant: if
    [{ rw_tyvars = tyvars; rw_vars = sv; rw_conds = φ; rw_rw = (l,r); }]
    is a rewrite rule, then:
    - sv ⊆ FV(l)
    - ((FV(r) ∪ FV(φ)) ∩ sv) ⊆ FV(l) *)
type rw_rule = {
  rw_params : Params.t;              (** parameters of the rule (polymorphisme) *)
  rw_system : SE.t;                  (** systems the rule applies to *)
  rw_vars   : Vars.tagged_vars;      (** term variables *)
  rw_conds  : Term.term list;        (** premises *)
  rw_rw     : Term.term * Term.term; (** pair (source, destination) *)
  rw_kind   : rw_kind;
  rw_bound  : Concrete.bound;
}

val pp_rw_rule : rw_rule formatter

(*------------------------------------------------------------------*)
val check_rule : rw_rule -> unit

val pat_to_rw_rule :
  ?loc:Location.t ->
  destr_eq  : (Term.term -> (Term.term * Term.term) option) ->
  destr_not : (Term.term -> (            Term.term) option) ->
  SE.t ->
  rw_kind ->
  [< `LeftToRight | `RightToLeft ] ->
  (Term.term*Concrete.bound) Term.pat ->
  rw_rule
