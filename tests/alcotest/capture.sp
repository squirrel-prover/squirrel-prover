abstract a : message
abstract b : message
abstract f : message->message

axiom one : f(a)=a
axiom two : forall x:message, (forall x:message, f(x)=a) => f(x)=b

system null.

goal f(a)=b.
Proof.
  intros.
  apply two to a.
  apply one.
Qed.
