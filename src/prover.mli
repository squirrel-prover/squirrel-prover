(** Infrastructure for interactive proofs:
    current lemma, current goals.
    It contains the state of the proof and the history as mutable states. *)

module L = Location
module SE = SystemExpr

module TS = LowTraceSequent

type lsymb = Theory.lsymb

(** Return the name of the goal currently being proved, if any. *)
val current_goal_name : unit -> string option

val get_current_system : unit -> SE.context option

(** Current mode of the prover:
    - [GoalMode] : waiting for the next goal.
    - [ProofMode] : proof of a goal in progress.
    - [WaitQed] : finished proof, waiting for closure.
    - [AllDone] : everything is done, waiting to leave the prover.
*)
type prover_mode = GoalMode | ProofMode | WaitQed | AllDone

val unnamed_goal : unit -> lsymb

(*------------------------------------------------------------------*)
(** {2 History management} *)

type proof_state

(** Abort the current proof. *)
val abort : unit -> unit

(** Get the current prover state. *)
val get_state : prover_mode -> Symbols.table -> proof_state

(** Get the first subgoal.
    @raise Not_found if there is no subgoal or current goal. *)
val get_first_subgoal : unit -> Goal.t

(** Restore a proof state. *)
val reset_from_state : proof_state -> prover_mode * Symbols.table

(*------------------------------------------------------------------*)
(** {3 Stateful interface} *)

(** Set the proof_state to its initial state. *)
val reset : unit -> unit

(** Save the current prover state. *)
val save_state : prover_mode -> Symbols.table -> unit

(** Restore the n-th previous prover state and return the
  * corresponding prover mode. *)
val reset_state : int -> prover_mode * Symbols.table

(** Push a new empty proof state history in the stack, to enter an `include` *)
val push_pt_history : unit -> unit

(** Pop a proof state history from the stack, to exit an `include` *)
val pop_pt_history : unit -> unit

(** Pop all proof state history from the stack, when an `include` fails *)
val pop_all_pt_history : unit -> unit

(** Reset the state to the top of the proof state history (leaving the
    history unchanged). *)
val reset_to_pt_history_head : unit -> prover_mode * Symbols.table

(** Option management **)
type option_name =
  | Oracle_for_symbol of string

type option_val =
  | Oracle_formula of Term.term

type option_def = option_name * option_val

exception Option_already_defined

val get_option : option_name -> option_val option

val add_option : option_def -> unit

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


(** Registry for tactics on some kind of judgment *)
module ProverTactics : sig
  type judgment = Goal.t
  type tac = judgment Tactics.tac

  (* Allows to register a general tactic. Used when the arguments of the tactic
     are complex. *)

  val register_general :
    string -> tactic_help:tactic_help ->
    ?pq_sound:bool ->
    (TacticsArgs.parser_arg list -> tac) -> unit

  (* Register a macro, built using the AST. *)
  val register_macro :
    string -> ?modifiers:string list -> tactic_help:tactic_help ->
        ?pq_sound:bool ->
    TacticsArgs.parser_arg Tactics.ast -> unit

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

  val get : L.t -> string -> TacticsArgs.parser_arg list -> tac
  val pp : bool -> Format.formatter -> lsymb -> unit

  (* Print all tactics with their help. Do not print tactics without help
     string. *)
  val pps : Format.formatter -> unit -> unit
  val pp_list : Format.formatter -> unit -> unit
end

val pp_ast : Format.formatter -> TacticsArgs.parser_arg Tactics.ast -> unit

(*------------------------------------------------------------------*)
(** {2 User printing query} *)

(** User printing query *)
type print_query =
  | Pr_system    of SE.parsed_t option (* [None] means current system *)
  | Pr_statement of lsymb

(*------------------------------------------------------------------*)
(** Error handling *)

type error = L.t * string

exception Error of error

val error : L.t -> string -> 'a

val pp_error :
  (Format.formatter -> Location.t -> unit) -> 
  Format.formatter -> error -> unit

(*------------------------------------------------------------------*)
(** {2 Utilities for parsing} *)

type include_param = { th_name : lsymb; params : lsymb list }

(*------------------------------------------------------------------*)
type parsed_input =
  | ParsedInputDescr of Decl.declarations
  | ParsedSetOption  of Config.p_set_param

  | ParsedTactic of [ `Bullet of string |
                      `Brace of [`Open|`Close] |
                      `Tactic of TacticsArgs.parser_arg Tactics.ast ] list

  | ParsedPrint   of print_query
  | ParsedUndo    of int
  | ParsedGoal    of Goal.Parsed.t Location.located
  | ParsedInclude of include_param
  | ParsedProof
  | ParsedQed
  | ParsedAbort
  | ParsedHint of Hint.p_hint
  | EOF

(** Declare a new goal to the current goals, and returns it. *)
val add_new_goal :
  Symbols.table -> Goal.Parsed.t Location.located -> string * Goal.t

val add_proof_obl : Goal.t -> unit

(** From the name of the function, returns the corresponding formula. If no tag
   formula was defined, returns False. *)
val get_oracle_tag_formula : string -> Term.term

val pp_goal : Format.formatter -> unit -> unit

val is_proof_completed : unit -> bool

(** Complete the proofs, resetting the current goal to None. *)
val complete_proof : Symbols.table -> Symbols.table

(** [eval_tactic utac] applies the tactic [utac]. *)
val eval_tactic : TacticsArgs.parser_arg Tactics.ast -> unit

(** Insert a bullet in the proof script. *)
val open_bullet : Bullets.bullet -> unit

(** Open a brace in the proof script. *)
val open_brace : unit -> unit

(** Close a brace in the proof script. *)
val close_brace : unit -> unit

(** Initialize the prover state try to prove the first of the unproved goal. *)
val start_proof : [`NoCheck | `Check] -> string option
