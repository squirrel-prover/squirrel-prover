system null.
goal forall (t:timestamp), not(happens(t)) => not(happens(t)).
Proof.
  nosimpl(intros).
  apply H0.
Qed.