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
  use two with x; 1: by auto.
  intro x'.
  by use one with x'.
Qed.
