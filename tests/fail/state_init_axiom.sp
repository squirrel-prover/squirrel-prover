set autoIntro = false.

name n: index -> message

mutable kR(i:index) : message = n(i)

system null.

axiom stateReaderInit : forall (i:index), kR(i)@init = n(i).
axiom exists_idx : exists i:index, True.

goal absurdity : False.
Proof.
  use exists_idx.
  simpl_left.
  use stateReaderInit with i.
  (* It should not be possible to conclude using fresh,
  because n(i) appears in action descriptions parsed by
  the fresh tactic (in the init action).
  This was actually not the case before fixing the way
  states are initialized, because the fresh tactic do not
  iterate over elements in axioms. *)
  checkfail (by fresh Meq) exn GoalNotClosed.
Abort.
