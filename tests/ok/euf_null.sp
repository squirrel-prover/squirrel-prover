hash h
name k : message
name n : message
name m : message

system null.

goal one :
  h(m,k) <> h(n,k).

Proof.
  simpl.
  euf M0.
Qed.

goal two :
  n <> h(n,k).

Proof.
  simpl.
  euf M0.
Qed.