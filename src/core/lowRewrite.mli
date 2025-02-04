(** Rewriting types and functions which do not depend on [Match] *)

open Ppenv

(*------------------------------------------------------------------*)
module L   = Location
module SE  = SystemExpr

(*------------------------------------------------------------------*)
(** If an equality use the kind [UseLocalContext] then it cannot be
    rewritten in a global hypothesis nor in the bound.

    If it is [Global], it can be rewritten anywhere (putting aside the
    question of concrete vs asymptotic).

    Finally, if it is [Any] then it can be used as a [UseLocalContext]
    or [Global]. If it is used as [Global], the conditions in
    [rw_conds] may not use local hypotheses. *)
type kind =  UseLocalContext | Global | Any

val kind_comp : kind -> kind -> kind

val pp_kind : Format.formatter -> kind -> unit

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
  rw_kind   : kind;
  rw_bound  : LowConcrete.bound;
}

val pp_rw_rule : rw_rule formatter_p

(*------------------------------------------------------------------*)
val check_rule : rw_rule -> unit

val pat_to_rw_rule :
  ?loc:Location.t ->
  destr_eq  : (Term.term -> (Term.term * Term.term) option) ->
  destr_not : (Term.term -> (            Term.term) option) ->
  SE.t ->
  kind ->
  [< `LeftToRight | `RightToLeft ] ->
  (Term.term*LowConcrete.bound) Term.pat ->
  rw_rule

(** Create a simple **exact** rewriting rule [left ↦ right] that can
    be used in any context. *)
val simple_rw_rule :
  SE.arbitrary -> Symbols.table ->
  left:Term.term -> right:Term.term -> rw_rule
