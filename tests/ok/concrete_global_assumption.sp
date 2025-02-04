 abstract a : message
abstract b : message

axiom [any] ax : a = b => false <: Real.z.

system null.

global lemma _ (x:message) : [x = a && x = b <: Real.z] -> [false <: Real.z].
Proof.
  intro H.
  assert (x = a && x = b) as [H1 H2] by assumption.
  rewrite H1 in H2.
  by apply ax.
Qed.

include Real.


global lemma _ (x:message) : [x = a && x = b <: Real.of_int 1] -> [false <: Real.of_int 2].
Proof.
  intro H.
  assert (x = a && x = b) <: Real.of_int 1 as [H1 H2].
  by assumption.
  simpl.
  rewrite H1 in H2.
  by apply ax.
Qed.
