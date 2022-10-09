(** Tactics exploiting a name's freshness. *)

module TS = TraceSequent
module ES = EquivSequent

(** fresh trace tactic *)
val fresh_trace_tac :
  TacticsArgs.parser_args ->
  TS.sequent ->
  (TS.sequents -> (Tactics.tac_error -> 'a) -> 'a) ->
  (Tactics.tac_error -> 'a) ->
  'a

(** fresh equiv tactic *)
val fresh_equiv_tac :
  TacticsArgs.parser_args ->
  ES.sequent ->
  (ES.sequents -> (Tactics.tac_error -> 'a) -> 'a) ->
  (Tactics.tac_error -> 'a) ->
  'a
