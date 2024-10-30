(* Testing that, when changing context (here, due to the use of `trans`)
   equivalence hypotheses are not abusively kept. *)

system N = null.

abstract a : message.
abstract b : message.
abstract p : message -> bool.

global lemma [set: N/left; equiv: N/left,N/right] _ :
  equiv(diff(p a, p b)) ->
  equiv(diff(a,b)).
Proof.
  intro H.
  nosimpl trans [N/right,N/left]; 1,3: auto.
  (* For the remaining subgoal the assumption H should either
     be dropped or swapped. *)
  checkfail (ghave _ : equiv(diff(p a, p b)) by auto) exn GoalNotClosed.
Abort.
