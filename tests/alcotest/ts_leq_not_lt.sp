set autoIntro=false.

abstract ok : message
channel c
system !_i A:out(c,ok).

goal forall (i:index,j:index), A(i) <= A(j) => A(i) < A(j).
Proof.
  intro i j Hle.
Qed.
