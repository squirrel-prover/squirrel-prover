(*------------------------------------------------------------------*)
(** {2 Tactics syntax trees} *)
(** Prover tactics, and tables for storing them. *)

(** Tactic groups. *)
type tactic_group =
  | Logical       (** Sequent calculus logical properties. *)
  | Structural    (** Properties inherent to protocol,
                      names or builtin functions. *)
  | Cryptographic (** Cryptographic assumptions. *)
  | None          (** No group for user-defined tactics, i.e. macros. *)

(** Tactic metadata and documentation. *)
type tactic_help = {
  general_help  : string;
  detailed_help : string;
  usages_sorts  : TacticsArgs.esort list;
  tactic_group  : tactic_group
}

val dbg : ('a, Format.formatter, unit) format -> 'a
val bad_args : unit -> 'a

type judgment = Goal.t
type tac = judgment Tactics.tac

module AST : Tactics.AST_sig
  with type arg = TacticsArgs.parser_arg
  with type judgment = judgment

(** General-purpose tactic registration function. *)
val register_general :
  string -> tactic_help:tactic_help ->
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

val register : string -> tactic_help:tactic_help ->
  ?pq_sound:bool ->
  (judgment -> judgment list) -> unit

val register_typed :
  string ->  general_help:string ->  detailed_help:string ->
  tactic_group:tactic_group ->
  ?pq_sound:bool ->
  ?usages_sorts : TacticsArgs.esort list ->
  ('a TacticsArgs.arg -> judgment -> judgment list) ->
  'a TacticsArgs.sort  -> unit

val get : bool -> Location.t -> string -> TacticsArgs.parser_arg list -> tac
val pp : bool -> Format.formatter -> Theory.lsymb -> unit

(* Print all tactics with their help. Do not print tactics without help
   string. *)
val pps : Format.formatter -> unit -> unit
val pp_list : Format.formatter -> unit -> unit
val pp_list_count : string -> unit

val get_help : Theory.lsymb -> unit
