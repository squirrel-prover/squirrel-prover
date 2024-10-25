global axiom [any] toto : [false].

system P = null.

global lemma [P] _ : [false].
Proof.
  apply toto.
Qed.

global lemma [set:P/left,P/left; equiv:P] _ : [false].
Proof.
  apply toto.
Qed.

global lemma [set:P/left,P/left; equiv:P/left,P/left] _ : [false].
Proof.
  apply toto.
Qed.
