type state
(** Set the proof_state to its initial state. *)
val init : unit -> state

val add_proof_obl : Goal.t -> state -> state

(** Return the name of the goal currently being proved, if any. *)
val get_current_system : state -> SystemExpr.context option

(** Return the the table of given state *)
val get_table : state -> Symbols.table
(** Set the the table of given state *)
val set_table : state -> Symbols.table -> state

(** Handler of parsed input *)
val tactic_handle : state -> [< `Brace of [< `Close | `Open ]
    | `Bullet of string
    | `Tactic of TacticsArgs.parser_arg Tactics.ast ] 
  -> state

(** return a copy of the current prover state. *)
val copy : state -> state

val is_proof_completed : state -> bool

(** Return the name of the goal currently being proved, if any. *)
val current_goal_name : state -> string option

val pp_goal : state -> Format.formatter -> unit -> unit

(** Complete the proofs, resetting the current goal to None. *)
val complete_proof : state -> state

val add_hint : state -> Hint.p_hint -> state

(** Declare a new goal to the current goals, and returns it. *)
val add_new_goal : state -> Goal.Parsed.t Location.located -> state 

(** Initialize the prover state try to prove the first of the unproved goal. *)
val start_proof : state -> [`Check | `NoCheck] -> (string option * state) 

(** Abort the current proof. *)
val abort : state -> state

(* ↓ for html ↓ *)

(** Get the first subgoal.
    @raise Not_found if there is no subgoal or current goal. *)
val get_first_subgoal : state -> Goal.t
