channel c

abstract ok : message
name n : message

system out(c,n XOR ok).

axiom len_ok : len(ok) = len(n).

equiv test.
Proof.
  induction t.
  expandall.
  fa 0; fa 1; fa 1.
  xor 1.
  yesif 1.
  apply len_ok.
Qed.
