set autoIntro=false.

system null.

goal forall (t:timestamp,tau:timestamp), t <= pred(tau) => t < tau.
Proof.
  simpl.
Qed.
