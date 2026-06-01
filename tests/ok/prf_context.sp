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
  fa 1.
  fresh 1. by assumption.
  fresh 1. by assumption.
  by assumption.    
Qed.
