(** Tactics exploiting a name's freshness. *)

module TS = TraceSequent

(** fresh trace tactic *)
val fresh_tac :
  TacticsArgs.parser_args ->
  TS.sequent ->
  (TS.sequents -> (Tactics.tac_error -> 'a) -> 'a) ->
  (Tactics.tac_error -> 'a) ->
  'a
