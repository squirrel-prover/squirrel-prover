module Pos = Match.Pos

(*------------------------------------------------------------------*)
include module type of LowRewrite

(*------------------------------------------------------------------*)
type error = 
  | NothingToRewrite
  | MaxNestedRewriting
  | RuleBadSystems of string

(*------------------------------------------------------------------*)
(** Try to do a rewrite at head position in a term.
    Return: rewritten term, proof obligations *)
val rewrite_head :
  Symbols.table ->
  Vars.env ->
  Macros.expand_context ->
  Hyps.TraceHyps.hyps Lazy.t ->
  SE.t ->
  rw_rule ->
  Term.term ->
  (Term.term * (SE.arbitrary * Term.term) list) option

(*------------------------------------------------------------------*)
type rw_res = Equiv.any_form * (SE.context * Term.term) list

type rw_res_opt = 
  | RW_Result of rw_res
  | RW_Failed of error

(*------------------------------------------------------------------*)
val rewrite :
  Symbols.table ->
  Vars.env ->                   (* used to get variable tags when matching *)
  SE.context ->
  Macros.expand_context ->
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
  Vars.env ->                   (* used to get variable tags when matching *)
  SE.context ->
  Macros.expand_context ->
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
      resp., empty and the [system] we are rewriting in. 

    If [strict] is true, rewriting cannot fail. *)
val high_rewrite :
  mode : [`TopDown of bool | `BottomUp] ->
  strict : bool ->
  Symbols.table ->
  Vars.env ->
  SE.t ->
  (Vars.vars -> Pos.pos -> rw_rule option) ->
  Term.term ->
  Term.term 
