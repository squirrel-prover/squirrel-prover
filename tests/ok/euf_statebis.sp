set autoIntro=false.

mutable s : message = empty
hash h
name k : message
system s := s.

goal forall tau:timestamp, output@tau <> h(zero,k).
Proof.
  intro tau Heq.
  euf Heq.
Qed.
