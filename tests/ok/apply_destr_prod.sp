system null.

abstract P : boolean.
abstract Q : boolean.

(*------------------------------------------------------------------*)
lemma _ : (P => Q) => P => Q. 
Proof. 
  intro H U. 
  apply H.
  clear H.
  assumption.
Qed.

lemma _ : (P => Q) => P => Q. 
Proof. 
  intro H. 
  apply H.
Qed.

(*------------------------------------------------------------------*)
lemma _ (a,b : index): (P => a <> b) => P => (a <> b). 
Proof. 
  intro H U. 
  apply H.
  assumption.
Qed.

lemma _ (a,b : index): (P => a <> b) => P => (a <> b). 
Proof. 
  intro H. 
  apply H.
Qed.
