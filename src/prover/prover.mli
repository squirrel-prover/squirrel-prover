(** {2 Prover state} 
   is composed by :
   - goals proofs obligation and lemma remaining to be proved
   - table of symbols
   - current_goal if there is one
   - subgoals associated sequent that has to be proved (i.e. the
   root of the required proof tree)
   - bullets (path trough a proof tree under contstruction)
  
    The term "goal" refers to two things below:

    - A toplevel goal declaration (i.e. a lemma)
      which is represented (with some redundancy) by a [Goal.statement]
      and a [Goal.t] which is the associated sequent that has to be
      proved, i.e. the root of the required proof tree.

    - A sequent that has to be proved (i.e. a node in a proof tree)
      which is represented by a [Goal.t].

    For now we use the adjectives toplevel and inner to distinguish
    the two kinds of goals. *)

open Squirrelcore

exception Unfinished

type state

(** Set the proof_state to its initial state. *)
val init' : unit -> state

(** add proof obligation *)
val add_proof_obl : Goal.t -> state -> state

(** add declarations *)
val add_decls : state -> Decl.declarations -> state * Goal.t list

val get_current_system : state -> SystemExpr.context option

(** Return current goal *)
val get_current_goal : state -> ProverLib.pending_proof option

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

(** do tactic with or without check of parsed input *)
val do_tactic' : ?check:[`Check | `NoCheck] -> state ->
  ProverLib.bulleted_tactics -> state

val is_proof_completed : state -> bool

(** If current proof is completed change prover_mode and 
* printout informations *)
val try_complete_proof : state -> state

(** Only switch prover_mode to AllDone → to finish program *)
val do_eof : state -> state

(** Return the name of the goal currently being proved, if any. *)
val current_goal_name : state -> string option

val pp_subgoals : state -> Format.formatter -> unit -> unit

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
  state -> ProverLib.search_query -> 
    (Lemma.lemma * Equiv.any_form list) list

(** Manage print query *)
val do_print : state -> ProverLib.print_query -> unit

(** Print out terms that match t pattern *)
val do_search : state -> ProverLib.search_query -> unit

(* ↓ for html ↓ *)

(** Get the first subgoal.
    @raise Not_found if there is no subgoal or current goal. *)
val get_first_subgoal : state -> Goal.t


(** Print goal *)
val pp_goal : state -> Format.formatter -> unit -> unit

(** Return Toplevel.PROVER in init state *)
val init : ?withPrelude:bool -> unit -> state

(** do tactics ! *)
val do_tactic : ?check:[`Check | `NoCheck] -> state ->
  Sedlexing.lexbuf -> ProverLib.bulleted_tactics ->  state

(** print current goal *)
val do_print_goal : state -> unit

(** Start a proof : initialize the prover state and set
 * prover_state regarding to a given `Check mode *)
val do_start_proof : ?check:[ `Check | `NoCheck ] -> state ->
  state

(** Add given parsed goal and print it out *)
val do_add_goal : state -> Goal.Parsed.t Location.located ->
  state

(** set param/option from Config (Alias for set_param) *)
val do_set_option : state -> Config.p_set_param -> state

(** Complete the proofs, resetting the current goal to None and
 * print exiting proof *)
val do_qed : state -> state

(** Add declarations to the table and print new proof obligations *)
val do_decls : state -> Decl.declarations -> state

(** Evaluate the given input and return new state *)
val do_command : ?main_mode:[`Stdin | `File of string]  -> ?file_stack:Driver.file list -> ?test:bool -> ?check:[`Check | `NoCheck] -> state ->
  Driver.file -> ProverLib.input -> state

(** Execute the given sentence and return new state *)
val exec_command : ?check:[`Check | `NoCheck] -> ?test:bool ->
  string -> state -> state 

(** Execute the given string and return new state *)
val exec_all : ?check:[`Check | `NoCheck] -> ?test:bool -> state
  -> string -> state

(** Run the given squirrel file *)
val run : ?test:bool -> string -> unit
