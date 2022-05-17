set autoIntro=false.

channel c

system new n; out(c,n).

include Basic.

equiv test.
Proof.
  induction t.

  auto.

  expandall.
  fa 0; fa 1; fa 1.
  fresh 1.
  by rewrite if_true in 1.
Qed.
