(** {2 Squirrel tactics} *)

(** Prover tactics, and tables for storing them. *)

val dbg : ('a, Format.formatter, unit) format -> 'a
val bad_args : unit -> 'a

type judgment = Goal.t
type tac = judgment Tactics.tac

module AST : Tactics.AST_sig
  with type arg = TacticsArgs.parser_arg
  with type judgment = judgment

(** General-purpose tactic registration function. *)
val register_general :
  string ->
  ?pq_sound:bool ->
  (TacticsArgs.parser_arg list -> tac) -> unit

(* Register a macro, built using the AST. *)
val register_macro : string -> AST.t -> unit

(* The remaining functions allow to easily register a tactic,
   without having to manage type conversions, or worry about the
   proper use of continuations in the tactics type.
   It is simply required to give a function over judgments,
   either without arguments (for [register])
   or with typed arguments (for [register_typed]). *)

val register : string ->
  ?pq_sound:bool ->
  (judgment -> judgment list) -> unit

val register_typed :
  string ->
  ?pq_sound:bool ->
  ('a TacticsArgs.arg -> judgment -> judgment list) ->
  'a TacticsArgs.sort  -> unit

val get :
  post_quantum:bool -> loc:Location.t ->
  string -> TacticsArgs.parser_arg list -> tac

(** Print usage count for all tactics. *)
val pp_list_count : string -> unit