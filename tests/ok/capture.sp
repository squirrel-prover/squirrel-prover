set autoIntro=false.

abstract a : message
abstract b : message
abstract f : message->message

system null.

axiom one : forall x:message, f(x)=a
axiom two : forall x:message, (forall x:message, f(x)=a) => f(x)=b.

goal _ (x:message): f(x)=b.
Proof.
  intro x.
  apply two to x. 
  intro x'.
  apply one to x'.
Qed.
