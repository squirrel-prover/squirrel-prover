(** Extends [LowTraceSequent] with function relying on the [Prover] module. *)

include module type of struct include LowTraceSequent end

include Sequent.S
  with type t         = LowTraceSequent.t
  and  type hyp_form  = LowTraceSequent.hyp_form
  and  type conc_form = LowTraceSequent.conc_form
