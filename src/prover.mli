(** Infrastructure for interactive proofs:
    proved lemmas, current lemma, current goals.
    It contains the state of the proof and the history as mutable states. *)

open Term
open Bformula
open Formula
open Logic

(** A goal of the prover is simply a name and a formula *)
type named_goal = string * formula

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
type gm_input = Gm_goal of string * formula | Gm_proof



(** History management. *)
exception Cannot_undo

type proof_state

(** Save the current prover state. The prover mode is the only external
    information required. *)
val save_state : prover_mode -> unit

(** Restore the n-th previous prover state and return the
  * corresponding prover mode. *)
val reset_state : int -> prover_mode

(** {2 Tactics syntax trees} *)

type tac_arg =
  | Subst of subst
  | Goal_name of string
  | Formula of Formula.formula
  | Function_name of fname
  | Int of int

module AST : Tactics.AST_sig
  with type arg = tac_arg and type judgment = Logic.Judgment.judgment

(** TODO documentation *)
exception Tactic_Soft_Failure of string

(** Placeholder for tactics on judgments *)
module Prover_tactics : sig
  type tac = Judgment.t Tactics.tac
  val register_general : string -> (tac_arg list -> tac) -> unit
  val register : string -> tac -> unit
  val register_subst : string -> (subst -> tac) -> unit
  val register_int : string -> (int -> tac) -> unit
  val register_formula : string -> (formula -> tac) -> unit
  val register_fname : string -> (fname -> tac) -> unit
  val register_macro : string -> AST.t -> unit
end

(** {2 Utilities for parsing} *)

(** [parse_args goalname ts] parses the arguments [ts] given  the environment
    defined by the goal [goalname]. It needs to access the list of proved goals.
*)
val parse_args : string -> Theory.term list -> Term.asubst list

val parse_args_exists : Theory.term list -> Term.asubst list

val parse_formula : Theory.formula -> formula

val get_goal_formula : string -> formula

(** Produces a goal formula given parsing informations. *)
val make_goal : Theory.formula -> formula

type parsed_input =
  | ParsedInputDescr
  | ParsedQed
  | ParsedTactic of AST.t
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
val eval_tactic : AST.t -> bool

(** Initialize the prover state try to prove the first of the unproved goal. *)
val start_proof : unit -> string option
