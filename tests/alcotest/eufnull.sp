hash h
name k : message
system null.

goal shouldntpass :
  h(k,k) = k => False.
Proof.
  simpl.
  euf M0.
Qed.
