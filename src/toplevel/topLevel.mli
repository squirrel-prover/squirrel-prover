open Squirrelcore
open Squirrelprover

exception Unfinished

(** {2 PROVER sig}
 *
 * The minimal signature for PROVER :
 * The module given to toplevel prover
 *)
module type PROVER = 
sig
  type state
  val init : unit -> state
  val add_proof_obl : Goal.t -> state -> state
  val get_current_system : state -> SystemExpr.context option
  val get_table : state -> Symbols.table
  val get_mode : state -> ProverLib.prover_mode
  val set_table : state -> Symbols.table -> state
  val tactic_handle : state -> ProverLib.bulleted_tactic -> state
  val do_tactic : ?check:[`Check | `NoCheck] -> state ->
    ProverLib.bulleted_tactics -> state
  val is_proof_completed : state -> bool
  val current_goal_name : state -> string option
  val pp_goal : state -> Format.formatter -> unit -> unit
  val complete_proof : state -> state
  val add_hint : state -> Hint.p_hint -> state
  val set_param : state -> Config.p_set_param -> state
  val add_new_goal : state -> Goal.Parsed.t Location.located -> state
  val start_proof : state -> [ `Check | `NoCheck ] -> string option * state
  val abort : state -> state
  val first_goal : state -> ProverLib.pending_proof
  val add_decls : state -> Decl.declarations -> state * Goal.t list
  val do_print : state -> ProverLib.print_query -> unit
  val do_search : state -> ProverLib.search_query -> unit
  val do_eof : state -> state
end

module type S = sig
    (** {TopLevel state}
     * composed with:
     * - PROVER.state the prover state (see Prover)
     * - Configs.params 
     * - option_defs (mainly used for oracles)
     * - prover_mode (keep trace of state of the current proof)
     *)
    type prover_state_ty
    type state = {
      prover_state : prover_state_ty; (* prover state *)
      params       : Config.params; (* save global params… *)
      option_defs  : ProverLib.option_def list; (* save global option_def *)
    }

    (** Print goal *)
    val pp_goal : state -> Format.formatter -> unit -> unit

    (** Return Toplevel.PROVER in init state *)
    val init : ?withPrelude:bool -> unit -> state

    (** do tactics ! *)
    val do_tactic : ?check:[`Check | `NoCheck] -> state ->
      Lexing.lexbuf -> ProverLib.bulleted_tactics ->  prover_state_ty

    (** return the Symbols table *)
    val get_table : state -> Symbols.table

    (** print current goal *)
    val do_print_goal : state -> unit

    (** Start a proof : initialize the prover state and set
     * prover_state regarding to a given `Check mode *)
    val do_start_proof : ?check:[ `Check | `NoCheck ] -> state ->
      prover_state_ty

    (** Add given parsed goal and print it out *)
    val do_add_goal : state -> Goal.Parsed.t Location.located ->
      prover_state_ty

    (** set param/option from Config *)
    val do_set_option : state -> Config.p_set_param -> state

    (** Complete the proofs, resetting the current goal to None and
     * print exiting proof *)
    val do_qed : state -> prover_state_ty

    (** Add declarations to the table and print new proof obligations *)
    val do_decls : state -> Decl.declarations -> prover_state_ty

    (** Print current system *)
    val do_print : state -> ProverLib.print_query -> unit
  
    (** Search a term and print matches *)
    val do_search : state -> ProverLib.search_query -> unit

    (** ↓ TODO remove params and options from globals ↓ *)
    (** Gets saved Config params *)
    val get_params : state -> Config.params

    (** Saves Config params *)
    val set_params : state -> Config.params -> state

    (** Get saved option_defs  *)
    val get_option_defs : state -> ProverLib.option_def list

    (** Saves option_defs *)
    val set_option_defs : state -> ProverLib.option_def list -> state

    (** Get prover mode *)
    val get_mode : state -> ProverLib.prover_mode

    (** Evaluate the given input and return new state *)
    val do_command : ?test:bool -> ?check:[`Check | `NoCheck] -> state ->
      Driver.file -> ProverLib.input -> state

    (** Execute the given sentence and return new state *)
    val exec_command : ?check:[`Check | `NoCheck] -> ?test:bool ->
      string -> state -> state 

    (** Execute the given string and return new state *)
    val exec_all : ?check:[`Check | `NoCheck] -> ?test:bool -> state
      -> string -> state

    (** Run the given squirrel file *)
    val run : ?test:bool -> string -> unit
end

(** {2 Toplevel prover}
 *
 * This is the module that manages a prover. 
 * It is a functor that takes a PROVER module.
 * The state contains option_defs (oracle), Configs params and
 * prover_mode (just a flag to know where we are in the proof, it can
 * be induced with prover_state).
 *
 * It does contains them but do not handle them yet… TODO
 * It only stores them for history purposes.
 * option_defs and Config.params are global refs (they have to be
 * managed statefully here)
 *
 * It mainly prints out results while calling PROVER functions.
 *)
module Make (Prover : PROVER) : S with type prover_state_ty =
                                         Prover.state
