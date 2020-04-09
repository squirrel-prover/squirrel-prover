channel c
abstract ok : message
abstract ko : message
system A: out(c,diff(ok,ko)); B: out(c,ok).

goal [left] output@A = ok.
Proof.
  simpl.
Qed.

goal output@B = ok.
Proof.
  simpl.
Qed.
