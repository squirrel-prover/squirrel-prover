

system null.

abstract P : boolean.
abstract Q : boolean.

(*------------------------------------------------------------------*)
goal _ : (P => Q) => P => Q. 
Proof. 
  intro H U. 
  apply H.
  clear H.
  assumption.
Qed.

goal _ : (P => Q) => P => Q. 
Proof. 
  intro H. 
  apply H.
Qed.

(*------------------------------------------------------------------*)
goal _ (a,b : index): (P => a <> b) => P => (a <> b). 
Proof. 
  intro H U. 
  apply H.
  assumption.
Qed.

goal _ (a,b : index): (P => a <> b) => P => (a <> b). 
Proof. 
  intro H. 
  apply H.
Qed.
