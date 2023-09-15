abstract ok : message
abstract ko : message

system null.

lemma _ :
  (try find (i : index) such that i=i in ok) = 
  (try find (i : index) such that i=i in ko).
Proof.
simpl.
Qed.
