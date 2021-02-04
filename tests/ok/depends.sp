set autoIntro=false.

channel c

system !_i in(c,x);out(c,x);in(c,x);out(c,x).

goal forall i:index, A(i) < A1(i).
Proof.
  intro i.
  depends A(i), A1(i).
  by auto.
Qed.
