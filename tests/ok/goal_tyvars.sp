

system null.

(*------------------------------------------------------------------*)
(* without type variables *)

goal eq_sym0 (x,y : message) : x = y => y = x.
Proof. auto. Qed.

goal _ (a,b : message) (c, d: message) : (b = a => c = d) => a = b => d = c.
Proof.
  intro > H H0.
  apply eq_sym0 in H0.
  apply eq_sym0.
  apply H.  
  assumption.
Qed.

(*------------------------------------------------------------------*)
(* check that wrong types do not match *)

goal _ ['a 'b] (a,b : 'a) : a = b => b = a.
Proof.
  intro H. 
  checkfail (
    try (apply eq_sym0);
    assumption
  ) exn NotHypothesis.
Abort.

(*------------------------------------------------------------------*)
(* with type variables *)

goal eq_sym ['a] (x,y : 'a) : x = y => y = x.
Proof. auto. Qed.

goal _ ['a 'b] (a,b : 'a) (c, d: 'b) : (b = a => c = d) => a = b => d = c.
Proof.
  intro H H0.
  apply eq_sym in H0.
  apply eq_sym.
  apply H.  
  assumption.
Qed.
