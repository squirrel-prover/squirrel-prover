set autoIntro = false.

abstract a : message
abstract b : message

axiom [any] ax : a = b => False.

system null.

global goal _ (x:message) : [x = a && x = b] -> [False].
Proof.
  intro H.
  checkfail destruct H as [H1 H2] exn Failure.
  localize H as H'; destruct H' as [H1 H2].
  rewrite H1 in H2.
  by apply ax.
Qed.
