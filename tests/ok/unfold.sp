op ptrue ['a] = fun x : 'a => true.

goal [any] _ : (fun i : index => true) = ptrue.
Proof.
  rewrite /ptrue //.
Qed.
