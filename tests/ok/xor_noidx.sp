

include Basic.

channel c

abstract ok : message
name n : message

system out(c,n XOR ok).

axiom len_ok : len(ok) = len(n).

equiv test.
Proof.
  induction t.

  auto.

  expandall.
  fa 0; fa 1; fa 1.
  xor 1.
  rewrite if_true in 1.
  simpl.
  by use len_ok.
  by fresh 1.
Qed.
