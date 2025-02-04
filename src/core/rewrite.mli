module Pos = Match.Pos

(*------------------------------------------------------------------*)
include module type of LowRewrite

(*------------------------------------------------------------------*)
type error = 
  | NothingToRewrite
  | MaxNestedRewriting

(*------------------------------------------------------------------*)
(** Try to do a rewrite at head position in a term.
    Return: rewritten term, proof obligations *)
val rewrite_head :
  param:Match.param ->
  concrete:bool ->
  Symbols.table ->
  Params.t ->
  Vars.env ->
  Hyps.TraceHyps.hyps ->
  SE.t ->
  rw_rule ->
  Term.term ->
  (Term.term * (SE.arbitrary * Term.term) list) option

(*------------------------------------------------------------------*)
type rw_res =
  Equiv.any_form *
  (SE.context * Term.term) list *
  LowConcrete.bound list

type rw_res_opt = 
  | RW_Result of rw_res
  | RW_Failed of error

(*------------------------------------------------------------------*)
val rewrite :
  param:Match.param -> 
  concrete:bool ->
  Symbols.table ->
  Params.t ->
  Vars.env ->                   (* used to get variable tags when matching *)
  SE.context ->
  Hyps.TraceHyps.hyps ->
  TacticsArgs.rw_count ->
  rw_rule ->
  Equiv.any_form -> 
  rw_res_opt
