name n : index->index->message

system null.

goal forall (j,j1,j2:index), n(j,j) = n(j1,j2) => j = j2.
Proof.
  intro *.
Qed.

goal forall (j,j1,j2:index), n(j,j) = n(j1,j2) => j = j1.
Proof.
  intro *.
Qed.
