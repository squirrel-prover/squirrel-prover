

abstract a : message
abstract b : message

system null.

goal _ (x, y, z: message) :
  x = a => y = b => x = y => (x = a => a = b => z = a) => (z = a).
Proof.
  intro H0 H1 H2 H3.
  rewrite H0 H1 in H2.
  revert H2 H0.
  assumption.  
Qed.
