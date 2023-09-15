op ptrue ['a] = fun x : 'a => true.

lemma [any] _ : (fun i : index => true) = ptrue.
Proof.
  rewrite /ptrue //.
Qed.
