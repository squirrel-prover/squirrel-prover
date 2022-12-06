(** {2 Prover state} 
 * is composed by :
 * - goals proofs obligation and lemma remaining to be proved
 * - table of symbols
 * - current_goal if there is one
 * - subgoals associated sequent that has to be proved (i.e. the
 * root of the required proof tree)
 * - bullets (path trough a proof tree under contstruction)
 *
    The term "goal" refers to two things below:

    - A toplevel goal declaration (i.e. a lemma)
      which is represented (with some redundancy) by a [Goal.statement]
      and a [Goal.t] which is the associated sequent that has to be
      proved, i.e. the root of the required proof tree.

    - A sequent that has to be proved (i.e. a node in a proof tree)
      which is represented by a [Goal.t].

    For now we use the adjectives toplevel and inner to distinguish
    the two kinds of goals. *)
type state

(** Set the proof_state to its initial state. *)
val init : unit -> state

(** add proof obligation *)
val add_proof_obl : Goal.t -> state -> state

(** add declarations *)
val add_decls : state -> Decl.declarations -> state * Goal.t list

val get_current_system : state -> SystemExpr.context option

(** Return the the table of given state *)
val get_table : state -> Symbols.table

(** Set the table of given state *)
val set_table : state -> Symbols.table -> state

(** Handler of parsed input *)
val tactic_handle : state -> ProverLib.bulleted_tactic -> state

(** return a copy of the current prover state. *)
val copy : state -> state

val is_proof_completed : state -> bool

(** Return the name of the goal currently being proved, if any. *)
val current_goal_name : state -> string option

val pp_goal : state -> Format.formatter -> unit -> unit

(** Complete the proofs, resetting the current goal to None. *)
val complete_proof : state -> state

(** TODO processDecl ? *)
val add_hint : state -> Hint.p_hint -> state

(** Declare a new goal to the current goals, and returns it. *)
val add_new_goal : state -> Goal.Parsed.t Location.located -> state 

(** Initialize the prover state try to prove the first of the unproved goal. *)
val start_proof : state -> [`Check | `NoCheck] -> (string option * state) 

(** Abort the current proof. *)
val abort : state -> state

(** Return first pending_proof. *)
val first_goal : state -> ProverLib.pending_proof

(* ↓ for html ↓ *)

(** Get the first subgoal.
    @raise Not_found if there is no subgoal or current goal. *)
val get_first_subgoal : state -> Goal.t
