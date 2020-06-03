hash h
name k : message
system null.

goal h(zero,h(zero,k)) <> h(zero,k).
Proof.
  intros.
  euf M0.
Qed.
