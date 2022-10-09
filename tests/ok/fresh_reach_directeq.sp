name n : index->message

system null.

goal _ (i,j:index): n(j) = n(i) => j = i.
Proof.
nosimpl(intro Heq).
nosimpl(fresh Heq; intro Heq2).
nosimpl(assumption).
Qed.
