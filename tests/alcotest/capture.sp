abstract a : message
abstract b : message
abstract f : message->message

system null.

axiom one : f(a)=a
axiom two (x:message): (forall x, f(x)=a) => f(x)=b.

lemma _: f(a)=b.
Proof.
  use two with a.
  use one.
Qed.
