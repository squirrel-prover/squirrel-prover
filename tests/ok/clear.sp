abstract a : message
abstract b : message

system null.

lemma _ (x, y, z: message) :
  x = a => y = b => x = y => (x = a => a = b => y = a) => (z = a).
Proof.
  intro H0 H1 H2 H3. 
  clear H0 H2.
  rewrite H1 in H3. 
  checkfail rewrite H0 in H3 exn Failure.
  checkfail rewrite H2 in H3 exn Failure.
  admit.  
Qed.

lemma _ (x, y, z: message) :
  x = a => y = b => x = y => (x = a => a = b => y = a) => (z = a).
Proof.
  intro H0 H1 H2 H3 {H0} {H2}. 
  rewrite H1 in H3.
  checkfail rewrite H0 in H3 exn Failure.
  checkfail rewrite H2 in H3 exn Failure.
  admit.  
Qed.

lemma _ (x, y, z: message) :
  x = a => y = b => x = y => (x = a => a = b => y = a) => (z = a).
Proof.
  intro H0 H1 H2 H3 {H0 H2}. 
  rewrite H1 in H3.
  checkfail rewrite H0 in H3 exn Failure.
  checkfail rewrite H2 in H3 exn Failure.
  admit.  
Qed.
