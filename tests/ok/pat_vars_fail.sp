

abstract f : message -> message.

system null.

goal _ : (forall (x : message), x = f (x)) => false.
Proof.
  intro H.
  checkfail have G := H _ exn CannotInferPats.
Abort.
