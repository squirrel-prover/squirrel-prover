

channel c
system
  in(c,x);
  let y = <x,x> in
  out(c,y).

goal _: happens(A) => output@A = <input@A,input@A>.
Proof.
 auto.
Qed.

goal _: output@A = <input@A,input@A>.
Proof.
 checkfail auto exn GoalNotClosed.
Abort.
