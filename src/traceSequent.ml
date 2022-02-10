(** Extends {!LowTraceSequent} with functions relying on the {!Prover} module. *)

include LowTraceSequent

include Sequent.Mk(struct
    module S = LowTraceSequent

    let to_general_sequent s = Goal.Trace s
  end)
