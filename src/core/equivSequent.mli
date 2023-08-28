(** Extends [LowEquivSequent] with function relying on the [Prover] module *)

include module type of struct include LowEquivSequent end

include Sequent.S
  with type t         = LowEquivSequent.t
  and  type hyp_form  = LowEquivSequent.hyp_form
  and  type conc_form = LowEquivSequent.conc_form
