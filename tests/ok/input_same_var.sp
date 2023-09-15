

channel c
system in(c,x);out(c,x);in(c,x);out(c,x).

lemma test :
  happens(A1) => output@A1 = input@A1.
Proof.
 auto.
Qed.

lemma test2 :
  output@A1 = input@A1.
Proof.
 checkfail auto exn GoalNotClosed.
Abort.
