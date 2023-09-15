

channel c
system
  in(c,x);
  let y = <x,x> in
  out(c,y).

lemma _: happens(A) => output@A = <input@A,input@A>.
Proof.
 auto.
Qed.

lemma _: output@A = <input@A,input@A>.
Proof.
 checkfail auto exn GoalNotClosed.
Abort.
