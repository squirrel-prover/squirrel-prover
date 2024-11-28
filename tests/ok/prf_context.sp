include Core.

channel c

hash h
name k : message

system new n; new m; out(c,m XOR h(n,k)).

equiv test.
Proof.
  induction t.

  auto.

  expandall.
  fa 0. fa 1; fa 1.
  prf 1.

  xor 1,n_PRF.
  rewrite if_true in 1.
  by rewrite namelength_m namelength_n_PRF.
  by fresh 1.
Qed.
