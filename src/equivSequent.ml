(** Extends [LowEquivSequent] with function relying on the [Prover] module *)

include LowEquivSequent

module ES = Sequent.Mk(LowEquivSequent)
include ES
