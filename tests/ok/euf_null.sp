

hash h
name k : message
name n : message
name m : message

system null.

goal one :
  h(m,k) <> h(n,k).

Proof.
  by intro Heq; euf Heq; auto.
Qed.

goal two :
  n <> h(n,k).

Proof.
  by intro Heq; euf Heq; auto.
Qed.
