module L   = Location
module SE  = SystemExpr
module Pos = Match.Pos

(*------------------------------------------------------------------*)
type error = 
  | NothingToRewrite
  | MaxNestedRewriting
  | RuleBadSystems of string

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
  rw_vars   : Vars.Sv.t;             (** term variables *)
  rw_conds  : Term.term list;        (** premises *)
  rw_rw     : Term.term * Term.term; (** pair (source, destination) *)
}

val pp_rw_rule : Format.formatter -> rw_rule -> unit

(*------------------------------------------------------------------*)
val check_rule : rw_rule -> unit

val pat_to_rw_rule :
  ?loc:Location.t ->
  destr_eq:(Term.term -> (Term.term * Term.term) option) ->
  SE.t ->
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
type rw_res = Equiv.any_form * (SE.context * Term.term) list

type rw_res_opt = 
  | RW_Result of rw_res
  | RW_Failed of error

(*------------------------------------------------------------------*)
val rewrite :
  Symbols.table ->
  SystemExpr.context ->
  Vars.env ->
  TacticsArgs.rw_count ->
  rw_rule ->
  Equiv.any_form -> 
  rw_res_opt

(*------------------------------------------------------------------*)
(** Same as [rewrite], but throws a user-level [Tactic] error if
    the rewriting fails  *)
val rewrite_exn :
  loc:L.t ->
  Symbols.table ->
  SystemExpr.context ->
  Vars.env ->
  TacticsArgs.rw_count ->
  rw_rule ->
  Equiv.any_form -> 
  rw_res

(*------------------------------------------------------------------*)
(** {2 Higher-level rewrite} *)

(** Rewrite a rule as much as possible, allowing to do it in a top-down or 
    bottom-up fashion.
    - the rewriting rule can depend on the position in the term. 
    - the rule conditions [rw_cond] and system [rw_system] must be, 
      resp., empty and the [system] we are rewriting in. *)
val high_rewrite :
  mode : [`TopDown of bool | `BottomUp] ->
  Symbols.table ->
  SE.t ->
  Vars.env ->
  (Vars.vars -> Pos.pos -> rw_rule option) ->
  Term.term ->
  Term.term 
