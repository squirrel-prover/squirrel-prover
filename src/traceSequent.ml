(** Extends {!LowTraceSequent} with functions relying on the {!Prover} module
  * to access proved goals. *)

include LowTraceSequent

include Sequent.Mk(LowTraceSequent)
