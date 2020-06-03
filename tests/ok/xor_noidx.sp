channel c

abstract ok : message
name n : message
axiom len_ok : len(ok) = len(n)

system out(c,n XOR ok).

equiv test.
Proof.
  induction t.
  expandall.
  fa 0; fa 1; fa 1.
  xor 1.
  yesif 1.
  apply len_ok.
Qed.
