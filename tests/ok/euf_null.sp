

hash h
name k : message
name n : message
name m : message

system null.

lemma one :
  h(m,k) <> h(n,k).

Proof.
  by intro Heq; euf Heq; auto.
Qed.

lemma two :
  n <> h(n,k).

Proof.
  by intro Heq; euf Heq; auto.
Qed.
