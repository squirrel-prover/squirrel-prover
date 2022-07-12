

channel c
system in(c,x);out(c,x);in(c,x);out(c,x).

goal test :
  happens(A1) => output@A1 = input@A1.
Proof.
 auto.
Qed.

goal test2 :
  output@A1 = input@A1.
Proof.
 checkfail auto exn GoalNotClosed.
Abort.
