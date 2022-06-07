

channel c
system X: in(c,x).

goal _: happens(X) => output@X = empty.
Proof.
  auto.
Qed.

(* fail if not happened *)
goal _: output@X = empty.
Proof.
 checkfail auto exn GoalNotClosed.
Abort.

