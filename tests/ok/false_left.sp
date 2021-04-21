set autoIntro=false.

system null.

goal _: False => exists x:index, x<>x.
Proof.
  auto.
Qed.
