set autoIntro=false.

mutable s : message
hash h
name k : message
system s := s.

goal _ (tau:timestamp) : happens(tau) => output@tau <> h(zero,k).
Proof.
  intro tau Hap Heq.
  euf Heq.
Qed.
