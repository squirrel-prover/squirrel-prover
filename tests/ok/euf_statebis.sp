set autoIntro=false.

mutable s : message
hash h
name k : message
system s := s.

goal _ (tau:timestamp) : output@tau <> h(zero,k).
Proof.
  intro tau Heq.
  euf Heq.
Qed.
