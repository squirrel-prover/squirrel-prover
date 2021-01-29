name n : index->message

system null.

goal forall (i,j:index) n(j) = n(i) => j = i.
Proof.
nosimpl(intro i j Heq).
nosimpl(fresh Heq; intro Heq2).
nosimpl(assumption).
Qed.
