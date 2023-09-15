

channel c
abstract ok : message
system let x = ok in out(c,x).
lemma _:   happens(A) => output@A = x@A.
Proof.
  auto.
Qed.
