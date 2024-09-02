(** {2 Prover} *)

open Squirrelcore
open Utils

(** A prover state contains everything that the prover needs to perform
    its operations in an immutable fashion (with a few exceptions):
    - a current table;
    - pending lemmas/theorems/obligations to be proved;
    - goals and bullets if in a proof;
    - etc. *)
type state



(** Return initial prover state. *)
val init : ?with_string_prelude:string option -> unit -> state

(** {2 Executing commands} *)

(** Exception raised in test mode
    when trying to close an incomplete proof using Qed. *)
exception Unfinished

(** Execute command from driver. *)
val do_command :
  ?driver_stack:Driver.t list ->
  ?test:bool ->
  ?check:[`Check | `NoCheck] ->
  state -> Driver.t -> ProverLib.input -> state

(** Execute the given sentence and return new state. *)
val exec_command :
  ?check:[`Check | `NoCheck] -> ?test:bool ->
  string -> state -> state

(** Execute commands from a string. *)
val exec_all :
  ?check:[`Check | `NoCheck] -> ?test:bool ->
  state -> string -> state

(** Execute commands from a file. *)
val run : ?test:bool -> string -> unit

(** {2 Accessors} *)

val get_system : state -> SystemExpr.context option

(** Return the table of given state. *)
val get_table : state -> Symbols.table

(** Return the prover mode. *)
val get_mode : state -> ProverLib.prover_mode

(** {2 Proof goals} *)

(** Return current goal. *)
val get_current_goal : state -> ProverLib.pending_proof option

(** Return the subgoals of given state. *)
val get_subgoals : state -> Goal.t list

(** Return the name of the goal currently being proved, if any. *)
val current_goal_name : state -> string option

(** Get the first subgoal.
    @raise Not_found if there is no subgoal or current goal. *)
val get_first_subgoal : state -> Goal.t

val pp_subgoals : state formatter

(** Print goal *)
val pp_goal : state formatter

(** Print current goal. *)
val do_print_goal : state -> unit

val is_proof_completed : state -> bool

(** {2 Misc}
    Inner functionalities for testing purposes. *)

val search_about :
  state -> ProverLib.search_query ->
  (Lemma.lemma * Equiv.any_form list) list

val do_set_option : state -> Config.p_set_param -> state
