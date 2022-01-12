set autoIntro=false.

abstract f : message -> message.

system null.

goal _ : (forall (x : message), x = f (x)) => false.
Proof.
  intro H.
  checkfail assert (G := H _) exn CannotInferPats.
Abort.
