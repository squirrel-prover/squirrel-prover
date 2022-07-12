system null.



(* check that variable naming allows to use any available variable name *)

goal _ (i0: index) :
  (exists (i : index), false) => false.
Proof. 
  intro B.
  destruct B as [i B].
  assumption.
Qed.

goal _ (i1: index) :
  (exists (i : index), false) => false.
Proof. 
  intro B.
  destruct B as [i0 B].
  assumption.
Qed.
  
