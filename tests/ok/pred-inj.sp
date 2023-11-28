system null.

lemma _ (t:timestamp,tau:timestamp) : t <= pred(tau) => t < tau.
Proof.
  auto.
Qed.
