(** Extends {!LowTraceSequent} with functions relying on the {!Prover} module
  * to access proved goals. *)

include LowTraceSequent

include Sequent.Mk(struct
    module S = LowTraceSequent

    let to_general_sequent s = Goal.Trace s
  end)
