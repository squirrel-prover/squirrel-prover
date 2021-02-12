set autoIntro=false.

channel c

system new n; out(c,n).

equiv test.
Proof.
  induction t.
  expandall.
  fa 0; fa 1; fa 1.
  fresh 1.
  yesif 1.
  by auto.
Qed.
