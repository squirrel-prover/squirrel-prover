channel c

system !_i in(c,x);out(c,x);in(c,x);out(c,x).

goal forall i:index, A1(i) < A1(i).
Proof.
  simpl.
  depends A1(i), A1(i).
Qed.
