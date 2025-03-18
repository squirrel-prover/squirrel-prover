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

(* ---------------------------------------------------------------- *)
global lemma _ (y : message) : 
  Let x = empty in
  [x = y] /\ [false] /\ [false] /\ [false] /\ [false].
Proof. 
  intro x. 
  try repeat split.
  + checkfail intro {x y} exn Failure.
    checkfail intro {x}   exn Failure.
    checkfail intro {y}   exn Failure.
    checkfail clear x     exn Failure.
    checkfail clear y     exn Failure.
    admit.
  + clear x.
    clear y.
    admit.    
  + clear x y.
    admit.
  + intro {x y}.
    admit.
  + intro {x}.
    intro {y}.
    admit.
Qed.

(* test whole-sequent clearing tactic `clear`  *)
global lemma _ (y : message) :  
  Let x = empty in
  Let z = x in
  Let z2 = (x,y,z) in
  [x = y] /\ [false] /\ [z2 = witness] /\ [false].
Proof. 
  intro *.
  try repeat split.
  + clear. 
    (* check that `x` and `y` have not been cleared *)
    have ?: x = y by admit.
    admit.
  + clear. 
    (* check that `x` and `y` have been cleared *)
    set x := 42. 
    set y := 42.
    admit.
  + clear.
    (* check that `x,y,z,z2` have not been cleared *)
    have ?: x = y && z = witness && z2 = witness by admit.
    admit.
  + clear.
    (* check that `x,y,z,z2` have been cleared *)
    set x  := 42. 
    set y  := 42.
    set z  := 42.
    set z2 := 42.
    admit.
Qed.
