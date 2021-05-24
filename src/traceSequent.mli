(** Extends [LowTraceSequent] with function relying on the [Prover] module. *)

include module type of struct include LowTraceSequent end

include Sequent.S
  with type t    = LowTraceSequent.t 
  and  type form = LowTraceSequent.form
