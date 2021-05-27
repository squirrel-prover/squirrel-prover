(** Extends [LowTraceSequent] with function relying on the [Prover] module. *)

include LowTraceSequent

module TS = Sequent.Mk(LowTraceSequent)
include TS
