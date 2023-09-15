include Basic.

(* test that infered types in the LHS are correctly substituted in the RHS *)
lemma [any] _ ['a] (phi:'a -> bool) :
 not (forall (a:'a), phi a) = exists (a:'a), not (phi a).
Proof.
  rewrite -(not_not (phi _)) -not_exists_1 //.
Qed.
