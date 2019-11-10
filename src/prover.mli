(** Infrastructure for interactive proofs:
    proved lemmas, current lemma, current goals.
    It contains the state of the proof and the history as mutable states. *)

open Term
open Logic

(** A goal of the prover is simply a name and a formula *)
type named_goal = string * formula

(** [current_goal] describes, if not None, the goal which is currently proved.
*)
val current_goal : named_goal option ref

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
type gm_input = Gm_goal of string * Term.formula | Gm_proof



(** History management. *)
exception Cannot_undo

(** A complete proof state:
    - [goals] contains the list of all declared goals.
    - [current_goal], if not None, points to the global goal at the beginning of
    the current proof.
    - [subgoals] contains the list of all subgoals of the current proof. It
    is initialized with the value of [current_goal].
    - [goals_proved] contains the list of proved goals.
    - [cpt_tag] is used to label and refer to displayed equations.
    - [prover_mode] stores the current prover_mode.
*)
type proof_state = { goals : named_goal list;
                     current_goal : named_goal option;
                     subgoals : Judgment.t list;
                     goals_proved : named_goal list;
                     cpt_tag : int;
                     prover_mode : prover_mode;
                   }

(** Save the current prover state. the prover mode is the only external
    information required.  *)
val save_state : prover_mode -> unit

(** Restore the n-th previous prover state and returns it. *)
val reset_state : int -> prover_mode

(** Tactic expressions and their evaluation.
    Cf the tactics module for their semantics. *)
type tac =
  | Admit : tac
  | Ident : tac

  | Left : tac
  | Right : tac
  | Intro : tac
  | Split : tac

  | Apply : (string * subst) -> tac

  | ForallIntro : tac
  | ExistsIntro : subst -> tac
  | AnyIntro : tac

  | GammaAbsurd : tac
  | ConstrAbsurd : tac

  | EqNames : tac
  | EqTimestamps : tac
  | EqConstants : fname -> tac

  (* | UProveAll : utac -> utac *)
  | AndThen : tac * tac -> tac
  | OrElse : tac * tac -> tac
  | Try : tac * tac -> tac
  | Repeat : tac -> tac

  | Euf : int -> tac
  | CollisionResistance : tac
  | Cycle : int -> tac

val pp_tac : Format.formatter -> tac -> unit

exception Tactic_Soft_Failure of string

(** [parse_args goalname ts] parses the arguments [ts] given  the environment
    defined by the goal [goalname]. It needs to access the list of proved goals.
*)
val parse_args : string -> Theory.term list -> Term.asubst list


(* Variable arguments, defined by a name and a kind (bool, messages, ...) *)
type args = (string * Theory.kind) list

(** Produces a goal formula given parsing informations. *)
val make_goal : (args * Theory.fact) *
                (args * Theory.fact) * Theory.fact * Theory.fact ->
  Term.formula

type parsed_input =
    ParsedInputDescr
  | ParsedQed
  | ParsedTactic of tac
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
val eval_tactic : tac -> bool

(** Initialize the prover state try to prove the first of the unproved goal. *)
val start_proof : unit -> string option
