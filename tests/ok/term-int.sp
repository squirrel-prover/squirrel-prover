include Basic.
include Int.
open Int.

op x = 42.
op y : int = 42.

lemma [any] _ : 21 + 21 = 42.
Proof. 
  reduce ~flags:[builtin]. 
  apply eq_refl.
Qed.

lemma [any] _ : 21 * 2 = 42.
Proof. 
  reduce ~flags:[builtin]. 
  apply eq_refl.
Qed.

lemma [any] _ : 44 - 2 = 42.
Proof. 
  reduce ~flags:[builtin]. 
  apply eq_refl.
Qed.
