channel c.
system default = !_i A : out(c,empty).

global axiom [default] toto (P : timestamp -> bool[const]) :
  [false].

global lemma [default] _ : [false].
Proof.
  have H := toto (fun (tau : timestamp) => exists (i : index), A i = tau); auto.
Qed.

global axiom [default] _ (P : timestamp -> bool[const]) :
  [false].

global lemma [default] _ : [false].
Proof.
  have H := toto (fun (tau : timestamp) => exists (i : _), A i = tau); auto.
Qed.

global lemma [default] _ : [false].
Proof.
  have H := toto (fun (tau : _) => exists (i : _), A i = tau); auto.
Qed.

global lemma [default] _ : [false].
Proof.
  have H := toto (fun (tau : _) => exists (i : index), A i = tau); auto.
Qed.
