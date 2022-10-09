abstract a : message
abstract b : message

axiom [any] ax : a = b => False.

system null.

global goal _ (x:message) : [x = a && x = b] -> [False].
Proof.
  intro H.
  assert (x = a && x = b) as [H1 H2] by assumption.
  rewrite H1 in H2.
  by apply ax.
Qed.
