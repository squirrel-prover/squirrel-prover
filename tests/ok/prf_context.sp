set autoIntro=false.

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
  yesif 1; 1: auto.

  xor 1,n_PRF.
  yesif 1.
  by namelength m, n_PRF.
  fresh 1.
  auto.
Qed.
