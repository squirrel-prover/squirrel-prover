abstract a : message
abstract b : message
abstract f : message->message

system null.

axiom one : forall x:message, f(x)=a
axiom two : forall x:message, (forall x:message, f(x)=a) => f(x)=b.

goal forall x:message, f(x)=b.
Proof.
  intros.
  apply two to x.
  apply one to x1.
Qed.
