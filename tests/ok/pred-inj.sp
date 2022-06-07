

system null.

goal _ (t:timestamp,tau:timestamp) : t <= pred(tau) => t < tau.
Proof.
  auto.
Qed.
