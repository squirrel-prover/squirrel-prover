mutable s : message
hash h
name k : message
system s := s.

goal forall tau:timestamp, output@tau <> h(zero,k).
Proof.
  intros.
  euf M0.
Qed.