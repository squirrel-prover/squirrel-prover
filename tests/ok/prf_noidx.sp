

include Basic.

channel c

hash h
name k : message

system new n; out(c,h(n,k)).

equiv test.
Proof.
  induction t.

  auto.

  expandall.
  fa 0; fa 1; fa 1.
  prf 1.
  by fresh 1.
Qed.
