abstract m:message
abstract n:message

system null.

axiom ax_both : m=n.

axiom [left:default] ax_left : n=m.

goal [left:default] _ : m=n.
Proof.
  use ax_both.
Qed.

goal [right:default] _ : m=n.
Proof.
  checkfail use ax_left exn NoAssumpSystem.
  use ax_both.
Qed.
