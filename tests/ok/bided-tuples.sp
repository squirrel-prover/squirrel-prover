name n : index->message

system null.

global goal _ (j:index[const]) : equiv(seq(i:index => n(i))) -> equiv(n(j)).
Proof.
  intro H.
  apply H. (* succeeds *)
Qed.

abstract ok : message.

global goal _ (j:index[const]) : equiv((ok,seq(i:index => n(i)))) -> equiv(n(j)).
Proof.
  intro H.
  try apply H. (* fails *)
Qed.

global goal _ (i:index[const]) :
  equiv(seq(i:index => (n(i),empty))) ->
  equiv(n(i)).
Proof.
  intro H.
  apply H.
Qed.
