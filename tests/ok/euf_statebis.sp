mutable s : message = empty
hash h
name k : message
system s := s.

lemma _ (tau:timestamp[param]) :
  happens(tau) => output@tau <> h(zero,k).
Proof.
  intro Hap Heq.
  euf Heq.
Qed.
