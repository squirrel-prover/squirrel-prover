

abstract x:message
abstract y:message

system null.

lemma _ : x=y.
Proof.
  nosimpl(assert x=y).
  admit.
  nosimpl(congruence).
  undo 3.
  try congruence.
Qed.
