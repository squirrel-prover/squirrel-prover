include Basic.

type T.

channel c.

abstract bob : index -> message.

system A : !_i out(c, bob (i)).

set debugConstr=true.

goal _ (i : index) : happens(A(i)) => output@A(i) = bob(i).
Proof. 
  intro Hap. 
  try rewrite /output.
  apply eq_refl. 
Qed.

abstract I : index.

goal _ : happens(A(I)) => output@A(I) = bob(I).
Proof. 
  intro Hap.
  try rewrite /output.
  apply eq_refl. 
Qed.
