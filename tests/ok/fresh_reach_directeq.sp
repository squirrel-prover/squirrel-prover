name n : index->message

system null.

lemma _ (i,j:index): n(j) = n(i) => j = i.
Proof.
  intro Heq.
  nosimpl (fresh Heq; intro Heq2).
  assumption.
Qed.
