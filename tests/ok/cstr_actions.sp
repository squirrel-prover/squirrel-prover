set autoIntro=false.

channel c
system !_i A: in(c,x); out(c,x).

goal forall (i:index,j:index),
  A(i) <= A(j) => i = j || A(i) < A(j).
Proof.
 by auto.
Qed.
