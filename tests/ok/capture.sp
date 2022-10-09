abstract a : message
abstract b : message
abstract f : message -> message

system null.

axiom one (x:message): f(x)=a
axiom two (x:message): (forall x:message, f(x)=a) => f(x)=b.

goal _ (x:message): f(x)=b.
Proof.
  use two with x; 1: auto.
  intro x'.
  by use one with x'.
Qed.

goal _ (z,u,w,x:message): (forall (x, y, x : message), f(x)=b) => f(z) = b.
Proof.
  intro H. 
  by use H with w, u, z.
Qed.
