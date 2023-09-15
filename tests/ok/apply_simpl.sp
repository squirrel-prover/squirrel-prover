include Basic.

(*------------------------------------------------------------------*)
lemma [any] _ ['a] (x : 'a) : 
  x = x.
Proof.
  apply eq_refl. 
Qed.

lemma [any] _ ['a] (z : 'a, y : 'a) : 
  (y, z, z, z) = (y, z, z, z).
Proof.
  apply eq_refl. 
Qed.
