system null.



(* check that variable naming allows to use any available variable name *)

lemma _ (i0: index) :
  (exists (i : index), false) => false.
Proof. 
  intro B.
  destruct B as [i B].
  assumption.
Qed.

lemma _ (i1: index) :
  (exists (i : index), false) => false.
Proof. 
  intro B.
  destruct B as [i0 B].
  assumption.
Qed.
  
