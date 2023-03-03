include Basic.

(*------------------------------------------------------------------*)
goal [any] _ ['a] (x : 'a) : 
  x = x.
Proof.
  apply eq_refl. 
Qed.

goal [any] _ ['a] (z : 'a, y : 'a) : 
  (y, z, z, z) = (y, z, z, z).
Proof.
  apply eq_refl. 
Qed.
