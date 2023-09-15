(* check that `congruence` handles tuple equalities *)

lemma [any] _ ['a 'b] (i1,i2 : 'a, j1,j2 : 'b) :
  (i1,j1) = (i2,j2) => i1 = i2 && j1 = j2.
Proof.
  intro H. 
  split. 
  + congruence.
  + congruence.
Qed.

lemma [any] _ ['a 'b 'c] (i1,i2 : 'a, j1,j2 : 'b, k1,k2 : 'c) :
  (i1,j1,k1) = (i2,j2,k2) => i1 = i2 && j1 = j2 && k1 = k2.
Proof.
  intro H. 
  split; 2:split. 
  + congruence.
  + congruence.
  + congruence.
Qed.
