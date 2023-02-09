set autoIntro = false.

name n: index -> message

mutable kR(i:index) : message = n(i)

system null.

axiom stateReaderInit : forall (i:index), kR(i)@init = n(i).

goal absurdity (i : index[const]) : false.
Proof.
  use stateReaderInit with i.
  (* It should not be possible to conclude using fresh,
  because n(i) appears in action descriptions parsed by
  the fresh tactic (in the init action).
  This was actually not the case before fixing the way
  states are initialized, because the fresh tactic does not
  (and must not) iterate over elements in axioms. *)
  checkfail (by fresh Meq) exn GoalNotClosed.
Abort.
