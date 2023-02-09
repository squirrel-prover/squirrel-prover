abstract ok : message
abstract ko : message

abstract f : message->message

name n : message
name m : message
name k : message

system null.

equiv testFresh : diff(f(ok),f(ok)),diff(n,m),k.

Proof.
  fresh 2; 1:auto.
  by fresh 0.
Qed.
