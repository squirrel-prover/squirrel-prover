name n : index * index -> message

system null.

set debugCompletion=true.
lemma _ (j,j1,j2:index): n(j,j) = n(j1,j2) => j = j2.
Proof.
  intro H. eqnames.
  auto.
Qed.

lemma _ (j,j1,j2:index): n(j,j) = n(j1,j2) => j = j1.
Proof.
  auto.
Qed.
