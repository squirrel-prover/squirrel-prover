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
  val do_search : state -> Theory.term -> unit
  val try_complete_proof : state -> state
  val do_eof : state -> state
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
module Make (Prover : PROVER) :
  sig
    (** {TopLevel state}
     * composed with:
     * - PROVER.state the prover state (see Prover)
     * - Configs.params 
     * - option_defs (mainly used for oracles)
     * - prover_mode (keep trace of state of the current proof)
     *)
    type state = {
      prover_state : Prover.state; (* prover state *)
      params       : Config.params; (* save global params… *)
      option_defs  : ProverLib.option_def list; (* save global option_def *)
    }

    (** Print goal *)
    val pp_goal : state -> Format.formatter -> unit -> unit

    (** Abort the current proof *)
    val abort : state -> state

    (** Return Toplevel.PROVER in init state *)
    val init : unit -> state

    (** If current proof is completed change prover_mode and printout
     * informations *)
    val try_complete_proof : state -> state

    (** Handle different parsed elements including Tactics ! *)
    val tactic_handle : state -> ProverLib.bulleted_tactic -> state

    (** return the Symbols table *)
    val get_table : state -> Symbols.table

    (** Only switch prover_mode to AllDone → to finish program *)
    val do_eof : state -> state

    (** Start a proof : initialize the prover state and set
     * prover_state regarding to a given `Check mode *)
    val do_start_proof : state -> [ `Check | `NoCheck ] -> state

    (** Add given parsed goal and print it out *)
    val do_add_goal : state -> Goal.Parsed.t Location.located -> state

    (** Add hint *)
    val do_add_hint : state -> Hint.p_hint -> state

    (** set param/option from Config *)
    val do_set_option : state -> Config.p_set_param -> state

    (** Complete the proofs, resetting the current goal to None and
     * print exiting proof *)
    val do_qed : state -> state

    (** Add declarations to the table and print new proof obligations *)
    val do_decls : state -> Decl.declarations -> state

    (** Print current system *)
    val do_print : state -> ProverLib.print_query -> unit
  
    (** Search a term and print matches *)
    val do_search : state -> Theory.term -> unit

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
  end
