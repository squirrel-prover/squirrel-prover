

name n : message
name m : message
abstract f : message->message
abstract h : message->message
system null.

lemma test (x:message, y:message) :
  n = m => False.
Proof.
  intro H.
  try auto.
Qed.

lemma _ (x:message, y:message) :
  x = y => False.
Proof.
  intro H.
  checkfail auto exn GoalNotClosed.
Abort.

lemma test2 (x:message, y:message) :
  f(n) = h(m) => False.
Proof.
  checkfail auto exn GoalNotClosed.
Abort.
