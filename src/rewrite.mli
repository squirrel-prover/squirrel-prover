module Pos  = Match.Pos

(*------------------------------------------------------------------*)
include module type of LowRewrite

(*------------------------------------------------------------------*)
type error = 
  | NothingToRewrite
  | MaxNestedRewriting
  | RuleBadSystems of string

(*------------------------------------------------------------------*)
(** Try to do a rewrite at head position in a term.  *)
val rewrite_head :
  Symbols.table ->
  Hyps.TraceHyps.hyps Lazy.t ->
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
  Hyps.TraceHyps.hyps ->
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
  Hyps.TraceHyps.hyps ->
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
