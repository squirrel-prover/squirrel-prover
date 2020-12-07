(** Infrastructure for interactive proofs:
    proved lemmas, current lemma, current goals.
    It contains the state of the proof and the history as mutable states. *)

open Term

module Goal : sig
  type t = Trace of TraceSequent.t | Equiv of EquivSequent.t
  val pp : Format.formatter -> t -> unit
  val pp_init : Format.formatter -> t -> unit
  val get_env : t -> Vars.env
end

(** A goal of the prover is simply a name and a formula *)
type named_goal = string * Goal.t

(** [current_goal] returns the current (sub)goal of the prover,
  * if any. *)
val current_goal : unit -> named_goal option

(** Current mode of the prover:
    - [InputDescr] : waiting for the process description.
    - [GoalMode] : waiting for the next goal.
    - [ProofMode] : proof of a goal in progress.
    - [WaitQed] : finished proof, waiting for closure.
*)
type prover_mode = InputDescr | GoalMode | ProofMode | WaitQed

(** Goal mode input types:
    - [Gm_goal f] : declare a new goal f.
    - [Gm_proof] : start a proof. *)
type gm_input = Gm_goal of string * Goal.t | Gm_proof


(** History management. *)

type proof_state

(** Set the proof_state to its initial state. *)
val reset : unit -> unit

(** Save the current prover state. The prover mode is the only external
    information required. *)
val save_state : prover_mode -> unit

(** Restore the n-th previous prover state and return the
  * corresponding prover mode. *)
val reset_state : int -> prover_mode

(** Option management **)
type option_name =
  | Oracle_for_symbol of string

type option_val =
  | Oracle_formula of Term.formula

type option_def = option_name * option_val

exception Option_already_defined

val get_option : option_name -> option_val option

val add_option : option_def -> unit

(** {2 Tactics syntax trees} *)
(** Prover tactics, and tables for storing them. *)

(* TODO module AST : Tactics.AST_sig
  with type arg = tac_arg and type judgment = Sequent.t *)

(** Registry for tactics on some kind of judgment *)
module type Tactics_sig = sig
  type judgment
  type tac = judgment Tactics.tac

  (* Allows to register a general tactic. Used when the arguments of the tactic
     are complex. *)
  val register_general :
    string -> ?help:string -> (TacticsArgs.parser_arg list -> tac) -> unit

  (* Register a macro, built using the AST. *)
  val register_macro :
    string -> ?modifiers:string list -> ?help:string ->
    TacticsArgs.parser_arg Tactics.ast -> unit

(* The remaining functions allows to easily register a tactic, without having to
   manage type conversions, or the tail recursvity. It is simply required to
   give a function over judgments, expecting some arguments of the given
   sort. *)
  val register : string -> ?help:string ->  (judgment -> judgment list) -> unit
  val register_typed : string -> ?help:string ->
    ('a TacticsArgs.arg -> judgment -> judgment list) ->
    'a TacticsArgs.sort  -> unit

  (* Allows to register a tactic, which is a specific orelse over other
     predefined tactics. It will try to apply the given tactics in the list, by
     giving them the arguments provided to the first tactic. Used to define
     polymorphic tactics, that will try to apply tactics of distinct types. *)
  val register_orelse :
    string -> ?help:string -> string list -> unit


  val get : string -> TacticsArgs.parser_arg list -> tac
  val pp : Format.formatter -> string -> unit

  (* Print all tactics with their help. Do not print tactics without help
     string. *)
  val pps : Format.formatter -> unit -> unit
end

val pp_ast : Format.formatter -> TacticsArgs.parser_arg Tactics.ast -> unit

module TraceTactics : Tactics_sig with type judgment = TraceSequent.t
module EquivTactics : Tactics_sig with type judgment = Goal.t

(** {2 Utilities for parsing} *)

exception ParseError of string

val get_goal_formula : string -> formula * Action.system

(** Produces a trace goal from a parsed formula,
  * for reasoning on the traces of the given system. *)
val make_trace_goal : system:Action.system -> Theory.formula -> Goal.t

(** Produces an equivalence goal from a sequence of parsed bi-terms. *)
val make_equiv_goal :
  Theory.env ->
  [ `Message of Theory.term | `Formula of Theory.formula ] list ->
  Goal.t

(* Produces an equivalence goal based on the process and the two system ids. *)
val make_equiv_goal_process : Action.single_system -> Action.single_system -> Goal.t

type parsed_input =
  | ParsedInputDescr
  | ParsedQed
  | ParsedTactic of TacticsArgs.parser_arg Tactics.ast
  | ParsedUndo of int
  | ParsedGoal of gm_input
  | EOF

(** Add a new goal to the current goals *)
val add_new_goal : named_goal -> unit

(** Store a proved goal, allowing to apply it. *)
val add_proved_goal : named_goal -> unit

(** Allows to define the tag formula corresponding to some function. Defining a function
   with such a tag, is equivalent to giving to the attacker a backdoor, allowing
   to compute the ouput of the function on all messages that satisfy the tag. *)
val define_oracle_tag_formula : string -> Theory.formula -> unit

(** From the name of the funciton, returns the corresponding formula. If no tag
   formula was defined, returns False. *)
val get_oracle_tag_formula : string -> Term.formula

(** Produce a fresh name for a unamed goal *)
val unnamed_goal : unit -> string

val pp_goal : Format.formatter -> unit -> unit

val is_proof_completed : unit -> bool

(** Complete the proofs, resetting the current goal to None. *)
val complete_proof : unit -> unit

(** [eval_tactic utac] applies the tactic [utac].
    Return [true] if there are no subgoals remaining. *)
val eval_tactic : TacticsArgs.parser_arg Tactics.ast -> bool

(** Initialize the prover state try to prove the first of the unproved goal. *)
     val start_proof : unit -> string option
