name n : index->message

system null.

global lemma _ (j:index[const]) : equiv(seq(i:index => n(i))) -> equiv(n(j)).
Proof.
  intro H.
  apply H. (* succeeds *)
Qed.

abstract ok : message.

global lemma _ (j:index[const]) : equiv((ok,seq(i:index => n(i)))) -> equiv(n(j)).
Proof.
  intro H.
  try apply H. (* fails *)
Qed.

global lemma _ (i:index[const]) :
  equiv(seq(i:index => (n(i),empty))) ->
  equiv(n(i)).
Proof.
  intro H.
  apply H.
Qed.
