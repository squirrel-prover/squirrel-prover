set autoIntro=false.

channel c
system A: in(c,x);out(c,x).

goal A <> init.
Proof.
  constraints.
Qed.
