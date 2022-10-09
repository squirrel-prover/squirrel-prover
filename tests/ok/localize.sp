abstract a : message
abstract b : message

axiom [any] ax : a = b => False.

system null.

global goal _ (x:message) : [x = a || x = b] -> [False].
Proof.
  intro H.
  checkfail destruct H as [_|_] exn Failure.
  localize H as H'.
  destruct H' as [_|_].
Abort.
