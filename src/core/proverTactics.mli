(*------------------------------------------------------------------*)
(** {2 Tactics syntax trees} *)
(** Prover tactics, and tables for storing them. *)


(* Define formats of help informations for tactics *)
type tactic_groups =
  | Logical       (* A logic tactic is a tactic that relies on the sequence calculus
                     logical properties. *)
  | Structural    (* A structural tactic relies on properties inherent to protocol,
                     on equality between messages, behaviour of ifthenelse,
                     action dependencies... *)
  | Cryptographic (* Cryptographic assumptions *)

(* The record for a detailed help tactic. *)
type tactic_help = { general_help : string;
                     detailed_help : string;
                     usages_sorts : TacticsArgs.esort list;
                     tactic_group : tactic_groups}

val pp_ast : Format.formatter -> TacticsArgs.parser_arg Tactics.ast -> unit
val dbg : ('a, Format.formatter, unit) format -> 'a
val bad_args : unit -> 'a

module AST : sig
  type arg = TacticsArgs.parser_arg
  type judgment = Goal.t
  type t = arg Tactics.ast
  val eval : bool -> string list -> t -> judgment Tactics.tac
  val eval_judgment : bool -> t -> judgment -> judgment list
  val pp : Format.formatter -> t -> unit
end

(** Registry for tactics on some kind of judgment *)
type judgment = Goal.t
type tac = judgment Tactics.tac

  (* Allows to register a general tactic. Used when the arguments of the tactic
     are complex. *)

val register_general :
  string -> tactic_help:tactic_help ->
  ?pq_sound:bool ->
  (TacticsArgs.parser_arg list -> tac) -> unit

(* Register a macro, built using the AST. FIXME never used ? *)
(* val register_macro : *)
(*   string -> ?modifiers:string list -> tactic_help:tactic_help -> *)
(*       ?pq_sound:bool -> *)
(*   TacticsArgs.parser_arg Tactics.ast -> unit *)

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
  tactic_group:tactic_groups ->
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
