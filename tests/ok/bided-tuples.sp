name n : index->message

system null.

global goal _ (j:index) : equiv(seq(i:index => n(i))) -> equiv(n(j)).
Proof.
  intro H.
  apply H. (* succeeds *)
Qed.

abstract ok : message.

global goal _ (j:index) : equiv((ok,seq(i:index => n(i)))) -> equiv(n(j)).
Proof.
  intro H.
  try apply H. (* fails *)
Qed.
