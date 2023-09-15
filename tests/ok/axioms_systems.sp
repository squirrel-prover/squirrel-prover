

abstract m:message
abstract n:message

system null.

axiom ax_both : m=n.

axiom [default/left] ax_left : n=m.

lemma [default/left] _ : m=n.
Proof.
  by use ax_both.
Qed.

lemma [default/right] _ : m=n.
Proof.
  checkfail use ax_left exn NoAssumpSystem.
  by use ax_both.
Qed.
