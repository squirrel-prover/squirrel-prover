channel c.

system new n; out(c,n).

include Core.

equiv test.
Proof.
  induction t.

  auto.

  expandall.
  fa 0; fa 1; fa 1.
  by fresh 1.
Qed.
