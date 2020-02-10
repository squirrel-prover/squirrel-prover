(** Infrastructure for interactive proofs:
    proved lemmas, current lemma, current goals.
    It contains the state of the proof and the history as mutable states. *)

open Term

module Goal : sig
  type t = Trace of Sequent.t | Equiv of EquivSequent.t
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

(** {2 Tactics syntax trees} *)

type tac_arg =
  | String_name of string
  | Formula of Term.formula
  | Function_name of fname
  | Int of int
  | Theory of Theory.term

(* TODO module AST : Tactics.AST_sig
  with type arg = tac_arg and type judgment = Sequent.t *)

(** Registry for tactics on some kind of judgment *)
module type Tactics_sig = sig
  type judgment
  type tac = judgment Tactics.tac
  val register_general : string -> ?help:string -> (tac_arg list -> tac) -> unit
  val register : string -> ?help:string -> tac -> unit
  val register_int : string -> ?help:string -> (int -> tac) -> unit
  val register_formula : string -> ?help:string -> (formula -> tac) -> unit
  val register_fname : string -> ?help:string -> (fname -> tac) -> unit
  val register_macro : string -> ?help:string -> tac_arg Tactics.ast -> unit
  val get : string -> tac_arg list -> tac
  val pp : Format.formatter -> string -> unit
  val pps : Format.formatter -> unit -> unit
end

val pp_ast : Format.formatter -> tac_arg Tactics.ast -> unit

module TraceTactics : Tactics_sig with type judgment = Sequent.t
module EquivTactics : Tactics_sig with type judgment = Goal.t

(** {2 Utilities for parsing} *)

val parse_formula : Theory.formula -> formula

val get_goal_formula : string -> formula

(** Produces a goal formula given parsing informations. *)
val make_trace_goal : Theory.formula -> Goal.t

type parsed_input =
  | ParsedInputDescr
  | ParsedQed
  | ParsedTactic of tac_arg Tactics.ast
  | ParsedUndo of int
  | ParsedGoal of gm_input
  | EOF

(** Add a new goal to the current goals *)
val add_new_goal : named_goal -> unit

(** Store a proved goal, allowing to apply it. *)
val add_proved_goal : named_goal -> unit

val pp_goal : Format.formatter -> unit -> unit

val is_proof_completed : unit -> bool

(** Complete the proofs, resetting the current goal to None. *)
val complete_proof : unit -> unit

(** [eval_tactic utac] applies the tactic [utac].
    Return [true] if there are no subgoals remaining. *)
val eval_tactic : tac_arg Tactics.ast -> bool

(** Initialize the prover state try to prove the first of the unproved goal. *)
val start_proof : unit -> string option
