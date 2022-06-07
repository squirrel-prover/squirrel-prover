

channel c
system in(c,x);out(c,x).

goal test :
  happens(A) => output@A = input@A.
Proof.
 auto.
Qed.

goal test2 :
  output@A = input@A.
Proof.
 checkfail auto exn GoalNotClosed.
Abort.
