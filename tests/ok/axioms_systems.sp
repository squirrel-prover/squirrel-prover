abstract m:message
abstract n:message

system null.

axiom ax_both : m=n.

axiom [default/left] ax_left : n=m.

goal [default/left] _ : m=n.
Proof.
  use ax_both.
Qed.

goal [default/right] _ : m=n.
Proof.
  checkfail use ax_left exn NoAssumpSystem.
  use ax_both.
Qed.
