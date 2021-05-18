set autoIntro=false.

channel c

system new n; out(c,n).

equiv test.
Proof.
  induction t.

  auto.

  expandall.
  fa 0; fa 1; fa 1.
  fresh 1.
  by yesif 1.
Qed.
