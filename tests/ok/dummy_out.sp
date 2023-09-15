

channel c
system X: in(c,x).

lemma _: happens(X) => output@X = empty.
Proof.
  auto.
Qed.

(* fail if not happened *)
lemma _: output@X = empty.
Proof.
 checkfail auto exn GoalNotClosed.
Abort.

