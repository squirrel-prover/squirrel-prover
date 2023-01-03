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

(** Execute a command : see @ProverLib.prover_input *)
val do_command : state -> ProverLib.prover_input -> state

(** Execute a command from string *)
val exec_command : string -> state -> state

(** add proof obligation *)
val add_proof_obl : Goal.t -> state -> state

(** add declarations *)
val add_decls : state -> Decl.declarations -> state * Goal.t list

val get_current_system : state -> SystemExpr.context option

(** Return the table of given state *)
val get_table : state -> Symbols.table

(** Return the subgoals of given state *)
val get_subgoals : state -> Goal.t list

(** Return the prover_mode *)
val get_mode : state -> ProverLib.prover_mode

(** Set the table of given state *)
val set_table : state -> Symbols.table -> state

(** Handler of parsed input *)
val tactic_handle : state -> ProverLib.bulleted_tactic -> state

val is_proof_completed : state -> bool

(** If current proof is completed change prover_mode and 
* printout informations *)
val try_complete_proof : state -> state

(** Only switch prover_mode to AllDone → to finish program *)
val do_eof : state -> state

(** Return the name of the goal currently being proved, if any. *)
val current_goal_name : state -> string option

val pp_goal : state -> Format.formatter -> unit -> unit

(** Complete the proofs, resetting the current goal to None. *)
val complete_proof : state -> state

(** TODO processDecl ? *)
val add_hint : state -> Hint.p_hint -> state

(** set param : from config *)
val set_param : state -> Config.p_set_param -> state

(** Declare a new goal to the current goals, and returns it. *)
val add_new_goal : state -> Goal.Parsed.t Location.located -> state 

(** Initialize the prover state try to prove the first of the unproved goal. *)
val start_proof : state -> [`Check | `NoCheck] -> (string option * state) 

(** Abort the current proof. *)
val abort : state -> state

(** Return first pending_proof. *)
val first_goal : state -> ProverLib.pending_proof

(** Returns terms that match t pattern in lemma *)
val search_about : 
  state -> Theory.term -> (Lemma.lemma * Term.t list) list

(** Manage print query *)
val do_print : state -> ProverLib.print_query -> unit

(** Print out terms that match t pattern *)
val do_search : state -> Theory.term -> unit

(* ↓ for html ↓ *)

(** Get the first subgoal.
    @raise Not_found if there is no subgoal or current goal. *)
val get_first_subgoal : state -> Goal.t
