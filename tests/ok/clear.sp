

abstract a : message
abstract b : message

system null.

goal _ (x, y, z: message) :
  x = a => y = b => x = y => (x = a => a = b => y = a) => (z = a).
Proof.
  intro H0 H1 H2 H3. 
  clear H0 H2.
  rewrite H1 in H3.
  admit.  
Qed.
