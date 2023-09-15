

channel c
system in(c,x);out(c,x).

lemma test :
  happens(A) => output@A = input@A.
Proof.
 auto.
Qed.

lemma test2 :
  output@A = input@A.
Proof.
 checkfail auto exn GoalNotClosed.
Abort.
