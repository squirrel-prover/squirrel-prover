set autoIntro=false.

channel c
system X: in(c,x).

goal _: output@X = empty.
Proof.
  auto.
Qed.
