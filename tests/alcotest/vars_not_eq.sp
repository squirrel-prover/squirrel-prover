set autoIntro=false.

name n : message
name m : message
abstract f : message->message
abstract h : message->message
system null.

goal test (x:message, y:message) :
  n = m => False.
Proof.
  intro x y _.
Qed.

goal test2 (x:message, y:message) :
  f(n) = h(m) => False.
Proof.
  intro *.
Qed.
