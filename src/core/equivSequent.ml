(** Extends [LowEquivSequent] with function relying on the [Prover] module *)

include LowEquivSequent

include Sequent.Mk(struct
    module S = LowEquivSequent

    let to_general_sequent s = Goal.Equiv s
    let to_global_sequent  s = s
  end)
