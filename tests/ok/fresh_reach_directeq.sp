name n : index->message

system null.

goal forall (i,j:index) n(j) = n(i) => j = i.
Proof.
nosimpl(intros).
nosimpl(fresh M0).
nosimpl(assumption).
Qed.
