

channel c
abstract ok : message
abstract ko : message
system A: out(c,diff(ok,ko)); B: out(c,ok).

goal [default/left] _ : happens(A) => output@A = ok.
Proof.
  auto.
Qed.

goal _ : happens(B) => output@B = ok.
Proof.
  auto.
Qed.
