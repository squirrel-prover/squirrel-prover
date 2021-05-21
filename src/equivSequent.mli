(** Extends [LowEquivSequent] with function relying on the [Prover] module *)

include module type of struct include LowEquivSequent end

include Sequent.S 
  with type t    = LowEquivSequent.t
  and  type form = LowEquivSequent.form
