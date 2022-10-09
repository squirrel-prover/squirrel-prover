name n : index * index -> message

system null.

goal _ (j,j1,j2:index): n(j,j) = n(j1,j2) => j = j2.
Proof.
  auto.
Qed.

goal _ (j,j1,j2:index): n(j,j) = n(j1,j2) => j = j1.
Proof.
  auto.
Qed.
